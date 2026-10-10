import OAI.Combinatorics.PlanarL1.Crossings

namespace OAI

section

namespace PlanarL1
/-! ## The metric counting step of the restricted packing bound
Padded surviving seeds lie near two short paths, giving a cardinality
estimate without a doubling assumption.
-/
namespace Packing

lemma same_bucket_close {t u ε : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (h : ⌊t / ε⌋₊ = ⌊u / ε⌋₊) : |t - u| < ε := by
  have ht₀ := Nat.floor_le (div_nonneg ht hε.le)
  have hu₀ := Nat.floor_le (div_nonneg hu hε.le)
  have ht₁ := Nat.lt_floor_add_one (t / ε)
  have hu₁ := Nat.lt_floor_add_one (u / ε)
  rw [h] at ht₀ ht₁
  have htu : t / ε - u / ε < 1 := by linarith
  have hut : u / ε - t / ε < 1 := by linarith
  rw [← sub_div, div_lt_one hε] at htu hut
  rw [abs_lt]
  constructor <;> linarith

/-- Points on two parameter intervals, separated by at least `ε` on each
interval, have cardinality at most `2 + 2*L/ε`. -/
theorem two_intervals_count {S : Type*} [Fintype S] {L ε : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) (side : S → Fin 2) (time : S → ℝ)
    (ht : ∀ i, 0 ≤ time i ∧ time i ≤ L)
    (hsep : ∀ i j, i ≠ j → side i = side j → ε ≤ |time i - time j|) :
    (Fintype.card S : ℝ) ≤ 2 + 2 * L / ε := by
  let bucket : S → Fin 2 × Fin (⌊L / ε⌋₊ + 1) := fun i =>
    (side i, ⟨⌊time i / ε⌋₊, Nat.lt_succ_of_le
      (Nat.floor_mono ((div_le_div_iff_of_pos_right hε).mpr (ht i).2))⟩)
  have hinj : Function.Injective bucket := by
    intro i j hij
    have hs : side i = side j := congrArg Prod.fst hij
    have hb : ⌊time i / ε⌋₊ = ⌊time j / ε⌋₊ := congrArg (fun x => x.2.val) hij
    by_contra hne
    exact (same_bucket_close hε (ht i).1 (ht j).1 hb).not_ge (hsep i j hne hs)
  have hc := Fintype.card_le_of_injective bucket hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hcreal : (Fintype.card S : ℝ) ≤ 2 * (⌊L / ε⌋₊ + 1) := by exact_mod_cast hc
  have hf := Nat.floor_le (div_nonneg hL hε.le)
  calc
    (Fintype.card S : ℝ) ≤ 2 * (⌊L / ε⌋₊ + 1) := hcreal
    _ ≤ 2 + 2 * L / ε := by nlinarith [mul_div_assoc (2 : ℝ) L ε]

/-- The two-path packing calculation, valid in any metric space. No bound on
all cells or all balls is asserted: the hypotheses refer only to the selected,
padded seeds and their explicitly assigned nearby path points. -/
theorem near_two_paths_count {X S : Type*} [PseudoMetricSpace X] [Fintype S]
    {L b ρ : ℝ} (hb : 0 < b) (hL : 0 ≤ L) (hρ : ρ ≤ b / 4)
    (seed : S → X) (path : Fin 2 → ℝ → X) (side : S → Fin 2) (time : S → ℝ)
    (ht : ∀ i, 0 ≤ time i ∧ time i ≤ L)
    (hne : ∀ i j, i ≠ j → b ≤ dist (seed i) (seed j))
    (hnear : ∀ i, dist (seed i) (path (side i) (time i)) ≤ ρ)
    (hpath : ∀ a t u, dist (path a t) (path a u) ≤ |t - u|) :
    (Fintype.card S : ℝ) ≤ 2 + 4 * L / b := by
  have hsep : ∀ i j, i ≠ j → side i = side j → b / 2 ≤ |time i - time j| := by
    intro i j hij hs
    have htri := dist_triangle4 (seed i) (path (side i) (time i))
      (path (side j) (time j)) (seed j)
    have hni := hnear i
    rw [hs] at hni
    have hnj := hnear j
    have hmid := hpath (side j) (time i) (time j)
    rw [hs, dist_comm (path (side j) (time j)) (seed j)] at htri
    have hbij := hne i j hij
    linarith
  have hc := two_intervals_count (by positivity : 0 < b / 2) hL side time ht hsep
  convert hc using 1
  ring

/-- Substitution of the actual packing constants: each path has length `4R`,
padded seeds are `0.01g` separated, and the source's near-path radius is at most
one quarter of that separation. -/
theorem surviving_seed_number {X S : Type*} [PseudoMetricSpace X] [Fintype S]
    {R g ρ : ℝ} (hg : 0 < g) (hR : 0 ≤ R) (hρ : ρ ≤ (0.01 * g) / 4)
    (seed : S → X) (path : Fin 2 → ℝ → X) (side : S → Fin 2) (time : S → ℝ)
    (ht : ∀ i, 0 ≤ time i ∧ time i ≤ 4 * R)
    (hne : ∀ i j, i ≠ j → 0.01 * g ≤ dist (seed i) (seed j))
    (hnear : ∀ i, dist (seed i) (path (side i) (time i)) ≤ ρ)
    (hpath : ∀ a t u, dist (path a t) (path a u) ≤ |t - u|) :
    Fintype.card S ≤ 2 + ⌈1600 * R / g⌉₊ := by
  have hreal := near_two_paths_count (by positivity : 0 < 0.01 * g)
    (by positivity : 0 ≤ 4 * R) hρ seed path side time ht hne hnear hpath
  have hcalc : 4 * (4 * R) / (0.01 * g) = 1600 * R / g := by ring
  rw [hcalc] at hreal
  have hceil := Nat.le_ceil (1600 * R / g)
  have : (Fintype.card S : ℝ) ≤ 2 + (⌈1600 * R / g⌉₊ : ℝ) := by linarith
  exact_mod_cast this

end Packing


end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Path

variable {n : ℕ} {M : Model n} {J I : Set ℝ}

/-- A specified visit of a finite switching path, retaining its traveled
arclength. Multiple visits of the same representative are not identified. -/
def AtTime : {i j : Fin n} → M.Path J i j → ℝ → ℝ → (Fin n × ℝ) → ℝ → Prop
  | i, _, .nil _, a, b, z, t => z.1 = i ∧ z.2 ∈ Set.uIcc a b ∧ t = |a-z.2|
  | i, _, .cons H _ _ p, a, b, z, t =>
      (z.1 = i ∧ z.2 ∈ Set.uIcc a H ∧ t = |a-z.2|) ∨ p.AtTime H b z (t-|a-H|)

lemma trace_atTime {i j : Fin n} (p : M.Path J i j) {a b : ℝ} {z : Fin n × ℝ}
    (hz : z ∈ p.trace a b) : ∃ t, p.AtTime a b z t := by
  induction p generalizing a with
  | nil i => exact ⟨|a-z.2|,hz.1,hz.2,rfl⟩
  | cons H hH hs p ih =>
    rcases hz with hz | hz
    · exact ⟨|a-z.2|,Or.inl ⟨hz.1,hz.2,rfl⟩⟩
    · obtain ⟨t,ht⟩ := ih hz
      exact ⟨|a-H|+t,Or.inr (by simpa only [add_sub_cancel_left] using ht)⟩

lemma atTime_split {i j : Fin n} (p : M.Path J i j) {a b t : ℝ} {z : Fin n × ℝ}
    (hz : p.AtTime a b z t) : ∃ (q : M.Path J i z.1) (r : M.Path J z.1 j),
      q.length a z.2 = t ∧ r.length z.2 b = p.length a b-t := by
  induction p generalizing a t with
  | nil i =>
    obtain ⟨hz,hs,ht⟩ := hz
    subst i
    exact ⟨.nil _,.nil _,ht.symm,by dsimp only [length]; linarith [abs_split hs]⟩
  | @cons i v j H hH hs p ih =>
    rcases hz with ⟨hz,hu,ht⟩ | hz
    · subst i
      refine ⟨.nil _,.cons H hH hs p,ht.symm,?_⟩
      dsimp only [length]
      linarith [abs_split hu]
    · obtain ⟨q,r,hq,hr⟩ := ih hz
      refine ⟨.cons H hH hs q,r,?_,?_⟩ <;> dsimp only [length] <;> linarith

lemma atTime_bounds {i j : Fin n} (p : M.Path J i j) {a b t : ℝ} {z : Fin n × ℝ}
    (hz : p.AtTime a b z t) : 0 ≤ t ∧ t ≤ p.length a b := by
  obtain ⟨q,r,hq,hr⟩ := p.atTime_split hz
  constructor <;> linarith [q.length_nonneg a z.2,r.length_nonneg z.2 b]

lemma vertical_offset {a b x y : ℝ} (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a b) :
    |x-y| = |(|a-x|)-(|a-y|)| := by
  rcases le_total a b with hab | hab
  · have hx' : a ≤ x := by rcases Set.mem_uIcc.mp hx with hx | hx <;> linarith
    have hy' : a ≤ y := by rcases Set.mem_uIcc.mp hy with hy | hy <;> linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hx'),abs_of_nonpos (sub_nonpos.mpr hy')]
    congr 1
    ring
  · have hx' : x ≤ a := by rcases Set.mem_uIcc.mp hx with hx | hx <;> linarith
    have hy' : y ≤ a := by rcases Set.mem_uIcc.mp hy with hy | hy <;> linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hx'),abs_of_nonneg (sub_nonneg.mpr hy')]
    have he : a-x-(a-y) = y-x := by ring
    rw [he,abs_sub_comm]

/-- Subpaths between actual arclength visits have no greater length than the
arclength difference. This is proved on the finite words, without assuming an
unconstructed continuous parametrization. -/
lemma between_atTime {i j : Fin n} (p : M.Path J i j) {a b t u : ℝ} {z w : Fin n × ℝ}
    (hz : p.AtTime a b z t) (hw : p.AtTime a b w u) :
    ∃ q : M.Path J z.1 w.1, q.length z.2 w.2 ≤ |t-u| := by
  induction p generalizing a t u with
  | nil i =>
    obtain ⟨hz,hs,ht⟩ := hz
    obtain ⟨hw,hr,hu⟩ := hw
    have he : z.1 = w.1 := hz.trans hw.symm
    let q : M.Path J z.1 w.1 := he ▸ .nil z.1
    refine ⟨q,?_⟩
    have hlen : q.length z.2 w.2 = |z.2-w.2| := by
      cases z with
      | mk zi zh =>
        cases w with
        | mk wi wh =>
          dsimp at he
          subst wi
          rfl
    rw [hlen,ht,hu,vertical_offset hs hr]
  | @cons i v j H hH hs p ih =>
    rcases hz with ⟨hz,hz',ht⟩ | hz <;> rcases hw with ⟨hw,hw',hu⟩ | hw
    · have he : z.1 = w.1 := hz.trans hw.symm
      let q : M.Path J z.1 w.1 := he ▸ .nil z.1
      refine ⟨q,?_⟩
      have hlen : q.length z.2 w.2 = |z.2-w.2| := by
        cases z with
        | mk zi zh =>
          cases w with
          | mk wi wh =>
            dsimp at he
            subst wi
            rfl
      rw [hlen,ht,hu,vertical_offset hz' hw']
    · obtain ⟨q,r,hq,_⟩ := p.atTime_split hw
      subst i
      refine ⟨.cons H hH hs q,?_⟩
      dsimp only [length]
      rw [hq]
      have he := abs_split hz'
      have htu : t ≤ u := by linarith [p.atTime_bounds hw,abs_nonneg (z.2-H)]
      rw [abs_of_nonpos (sub_nonpos.mpr htu)]
      linarith
    · obtain ⟨q,r,hq,_⟩ := p.atTime_split hz
      subst i
      let vq : M.Path J w.1 z.1 := .cons H hH hs q
      refine ⟨vq.reverse,?_⟩
      rw [length_reverse]
      change |w.2-H|+q.length H z.2 ≤ |t-u|
      rw [hq]
      have he := abs_split hw'
      have hut : u ≤ t := by linarith [p.atTime_bounds hz,abs_nonneg (w.2-H)]
      rw [abs_of_nonneg (sub_nonneg.mpr hut)]
      linarith
    · obtain ⟨q,hq⟩ := ih hz hw
      refine ⟨q,?_⟩
      have he : t-|a-H|-(u-|a-H|) = t-u := by ring
      rwa [he] at hq

lemma dist_atTime {i j root : Fin n} (p : M.Path J i j) (hJI : J ⊆ I)
    {a b t u : ℝ} (z w : M.Point I root)
    (hz : p.AtTime a b (z.column,z.height) t) (hw : p.AtTime a b (w.column,w.height) u) :
    dist z w ≤ |t-u| := by
  obtain ⟨q,hq⟩ := p.between_atTime hz hw
  exact (z.distance_le w (q.widen hJI)).trans (by simpa only [length_widen] using hq)

end PlanarL1.Columns.Model.Path

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- The source's two-path packing bound for the actual finite switching paths,
including all their vertical representatives and repeated visits. -/
theorem near_two_traces_count {S : Type*} [Fintype S] {L b ρ : ℝ}
    (hJI : J ⊆ I) (hb : 0 < b) (hL : 0 ≤ L) (hρ : ρ ≤ b/4)
    (start finish : Fin 2 → Fin n) (p : ∀ a, M.Path J (start a) (finish a))
    (A B : Fin 2 → ℝ) (hp : ∀ a, (p a).length (A a) (B a) ≤ L)
    (seed near : S → M.Point I root) (side : S → Fin 2)
    (htrace : ∀ i, ((near i).column,(near i).height) ∈
      (p (side i)).trace (A (side i)) (B (side i)))
    (hne : ∀ i j, i ≠ j → b ≤ dist (seed i) (seed j))
    (hnear : ∀ i, dist (seed i) (near i) ≤ ρ) :
    (Fintype.card S : ℝ) ≤ 2+4*L/b := by
  classical
  choose time htime using (fun i => (p (side i)).trace_atTime (htrace i))
  have ht : ∀ i, 0 ≤ time i ∧ time i ≤ L := by
    intro i
    exact ⟨((p (side i)).atTime_bounds (htime i)).1,
      ((p (side i)).atTime_bounds (htime i)).2.trans (hp (side i))⟩
  have hsep : ∀ i j, i ≠ j → side i = side j → b/2 ≤ |time i-time j| := by
    intro i j hij hs
    have hi := htime i
    rw [hs] at hi
    have hmid := (p (side j)).dist_atTime hJI (near i) (near j) hi (htime j)
    have htri := dist_triangle4 (seed i) (near i) (near j) (seed j)
    rw [dist_comm (near j) (seed j)] at htri
    linarith [hne i j hij,hnear i,hnear j]
  have hc := Packing.two_intervals_count (by positivity : 0 < b/2) hL side time ht hsep
  convert hc using 1
  ring

/-- Direct substitution of the manuscript constants, with no abstract
Lipschitz path or externally supplied parametrization. -/
theorem surviving_seed_traces_number {S : Type*} [Fintype S] {R g ρ : ℝ}
    (hJI : J ⊆ I) (hg : 0 < g) (hR : 0 ≤ R) (hρ : ρ ≤ (0.01*g)/4)
    (start finish : Fin 2 → Fin n) (p : ∀ a, M.Path J (start a) (finish a))
    (A B : Fin 2 → ℝ) (hp : ∀ a, (p a).length (A a) (B a) ≤ 4*R)
    (seed near : S → M.Point I root) (side : S → Fin 2)
    (htrace : ∀ i, ((near i).column,(near i).height) ∈
      (p (side i)).trace (A (side i)) (B (side i)))
    (hne : ∀ i j, i ≠ j → 0.01*g ≤ dist (seed i) (seed j))
    (hnear : ∀ i, dist (seed i) (near i) ≤ ρ) :
    Fintype.card S ≤ 2+⌈1600*R/g⌉₊ := by
  have hc := near_two_traces_count hJI (by positivity : 0 < 0.01*g)
    (by positivity : 0 ≤ 4*R) hρ start finish p A B hp seed near side htrace hne hnear
  have he : 4*(4*R)/(0.01*g) = 1600*R/g := by ring
  rw [he] at hc
  have hceil := Nat.le_ceil (1600*R/g)
  have : (Fintype.card S : ℝ) ≤ 2+(⌈1600*R/g⌉₊ : ℝ) := by linarith
  exact_mod_cast this

end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

/-- A connected low set lying on the far side of a chord has no vertex in
its open interval, provided neither endpoint belongs to that set. -/
lemma gap_of_chord {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {S : Set (Fin n)} (hS : (G.induce S).Preconnected) {a b c : Fin n}
    (hab : G.Adj a b) (ha : a ∉ S) (hb : b ∉ S) (hc : c ∈ S)
    (hcside : c < a ∨ b < c) : ∀ v ∈ S, v < a ∨ b < v := by
  intro v hv
  by_contra h
  obtain ⟨p⟩ := hS ⟨v,hv⟩ ⟨c,hc⟩
  let q := p.map (SimpleGraph.Embedding.induce S).toHom
  have hmem : ∀ t ∈ q.support, t ∈ S := by
    intro t ht
    obtain ⟨w,_,hw⟩ := List.mem_map.mp (by simpa only [q,SimpleGraph.Walk.support_map] using ht)
    exact hw ▸ w.property
  have hav : a ≠ v := fun he => ha (he ▸ hv)
  have hbv : b ≠ v := fun he => hb (he ▸ hv)
  have hvside : a < v ∧ v < b := by push Not at h; constructor <;> omega
  rcases chord_separation hnc hab q hvside hcside with hm | hm
  · exact ha (hmem a hm)
  · exact hb (hmem b hm)

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns

lemma not_consecutive_of_between {n : ℕ} {a b w c : Fin n}
    (hw : a < w ∧ w < b) (hc : c < a ∨ b < c) : ¬ Consecutive a b := by
  intro h
  rcases h with h | h | ⟨h,h'⟩ | ⟨h,h'⟩ <;>
    rcases hc with hc | hc <;> simp only [Fin.lt_def] at hw hc <;> omega

namespace Model.Path

variable {n : ℕ} {M : Model n} {J : Set ℝ}

lemma trace_start {i j : Fin n} (p : M.Path J i j) (a b : ℝ) :
    (i,a) ∈ p.trace a b := by
  cases p with
  | nil => exact ⟨rfl,Set.left_mem_uIcc⟩
  | cons => exact Or.inl ⟨rfl,Set.left_mem_uIcc⟩

lemma trace_end {i j : Fin n} (p : M.Path J i j) (a b : ℝ) :
    (j,b) ∈ p.trace a b := by
  induction p generalizing a with
  | nil => exact ⟨rfl,Set.right_mem_uIcc⟩
  | cons H _ _ p ih => exact Or.inr (ih H)

lemma trace_on_column {i j : Fin n} (p : M.Path J i j) {a b : ℝ}
    (ha : a ∈ J) {v : Fin n} (hv : v ∈ p.word.support) :
    ∃ H ∈ J, (v,H) ∈ p.trace a b := by
  induction p generalizing a with
  | nil i =>
    have he : v = i := by simpa only [word,SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
    exact ⟨a,ha,he,Set.left_mem_uIcc⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      exact ⟨a,ha,Or.inl ⟨rfl,Set.left_mem_uIcc⟩⟩
    · obtain ⟨T,hT,ht⟩ := ih hH hv
      exact ⟨T,hT,Or.inr ht⟩

/-- Every dart of the word is an actual switch at a height visited on both
of its representatives by the original path. -/
lemma dart_on_trace {i j : Fin n} (p : M.Path J i j) (a b : ℝ)
    (e : (M.activeGraph J).Dart) (he : e ∈ p.word.darts) :
    ∃ H ∈ J, H ∈ M.heights e.fst e.snd ∧
      (e.fst,H) ∈ p.trace a b ∧ (e.snd,H) ∈ p.trace a b := by
  induction p generalizing a with
  | nil => simp only [word,SimpleGraph.Walk.darts_nil,List.not_mem_nil] at he
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact ⟨H,hH,hs,Or.inl ⟨rfl,Set.right_mem_uIcc⟩,Or.inr (p.trace_start H b)⟩
    · obtain ⟨T,hT,ht,he₁,he₂⟩ := ih H he
      exact ⟨T,hT,ht,Or.inr he₁,Or.inr he₂⟩

end Model.Path

end PlanarL1.Columns

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}

namespace Point

/-- Vertical transfer to either representative of a switch costs at most the
width of the band, even if the two representatives are not equal as structures. -/
lemma dist_to_tip (e v : M.Point J root) {b : Fin n} {a : ℝ}
    (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a) (hv : v.column = e.column ∨ v.column = b) :
    dist v e ≤ a := by
  rcases hv with hv | hv
  · rw [v.dist_same_column e hv]
    exact hw v.height v.inBand e.height e.inBand
  · have hs' : e.height ∈ M.heights v.column e.column := by rw [hv,M.symm]; exact hs
    have hd := v.dist_le_switch e e.inBand hs'
    simpa only [sub_self,abs_zero,add_zero] using hd.trans
      (by simpa only [sub_self,abs_zero,add_zero] using hw v.height v.inBand e.height e.inBand)

end Point

namespace Field

/-- Descending paths are actual attained shortest switching paths, with the
manuscript's length domain and endpoint deficit, not assumed rays in a quotient. -/
structure Descent (F : M.Field J 1) (x : M.Point J root) (ε : ℝ) where
  target : M.Point J root
  path : M.Path J x.column target.column
  shortest : path.length x.height target.height = dist x target
  lower : (1:ℝ)/100000 ≤ path.length x.height target.height
  upper : path.length x.height target.height ≤ (1:ℝ)/50
  drop : F.eval target ≤ F.eval x-path.length x.height target.height+ε

namespace Descent

variable {F : M.Field J 1} {x : M.Point J root} {ε : ℝ}

/-- A visited column supplies an actual prefix point with both the total
length control and the almost-unit descending scalar estimate. -/
lemma column_prefix (D : F.Descent x ε) {v : Fin n} (hv : v ∈ D.path.word.support) :
    ∃ z : M.Point J root, z.column = v ∧ dist x z ≤ (1:ℝ)/50 ∧
      F.eval z ≤ F.eval x-dist x z+ε := by
  obtain ⟨T,hT,q,r,hqr⟩ := D.path.split_at_column x.inBand D.target.inBand hv
  let z : M.Point J root := ⟨v,T,hT,x.reachable.trans q.word.reachable⟩
  have hd := x.distance_le z q
  have hn := r.length_nonneg T D.target.height
  have hf := F.path_bound r ⟨T,hT⟩ ⟨D.target.height,D.target.inBand⟩
  norm_num only [NNReal.coe_one,one_mul] at hf
  have hzval : F.eval z-F.eval D.target ≤ r.length T D.target.height :=
    (le_abs_self _).trans hf
  have hshort := D.upper
  have hdrop := D.drop
  refine ⟨z,rfl,?_,?_⟩ <;> change dist x z ≤ q.length x.height T at hd <;> linarith

/-- Basic reach-to-tip bound used to show that a witness partner cannot lie
on the skipped side of a chord. -/
lemma near_tip (D : F.Descent x ε) (e : M.Point J root) {b : Fin n} {a : ℝ}
    (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hx : e.column < x.column ∧ x.column < b)
    (hz : D.target.column < e.column ∨ b < D.target.column) :
    dist x e ≤ (1:ℝ)/50+a := by
  have hadj : (M.activeGraph J).Adj e.column b := ⟨e.height,e.inBand,hs⟩
  obtain hv | hv := ColumnOrder.chord_separation (M.active_noncrossing J) hadj D.path.word hx hz
  · obtain ⟨v,hv,hlen,_⟩ := D.column_prefix hv
    have hd := e.dist_to_tip v hs hw (Or.inl hv)
    linarith [dist_triangle x v e]
  · obtain ⟨v,hv,hlen,_⟩ := D.column_prefix hv
    have hd := e.dist_to_tip v hs hw (Or.inr hv)
    linarith [dist_triangle x v e]

/-- The quantitative skipped-seed estimate `pack:near-path`: the absence of a
low separating tip truncates the actual descending prefix at j+ε+a. -/
lemma near_tip_of_not_low (D : F.Descent x ε) (hJ : IsClosed J)
    (e : M.Point J root) {b : Fin n} {a j : ℝ}
    (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hx : e.column < x.column ∧ x.column < b)
    (hz : D.target.column < e.column ∨ b < D.target.column)
    (hlow : F.eval x-j ≤ F.eval e) : dist x e ≤ j+ε+2*a := by
  have hadj : (M.activeGraph J).Adj e.column b := ⟨e.height,e.inBand,hs⟩
  have hvis := ColumnOrder.chord_separation (M.active_noncrossing J) hadj D.path.word hx hz
  have hcase {k : Fin n} (hk : k ∈ D.path.word.support) (he : k = e.column ∨ k = b) :
      dist x e ≤ j+ε+2*a := by
    obtain ⟨v,hv,_,hdrop⟩ := D.column_prefix hk
    have hd := e.dist_to_tip v hs hw (hv ▸ he)
    have hf := (F.lipschitz hJ root).dist_le_mul e v
    change dist (F.eval e) (F.eval v) ≤ (1:NNReal)*dist e v at hf
    rw [Real.dist_eq,NNReal.coe_one,one_mul,dist_comm e v] at hf
    have hr : F.eval e-F.eval v ≤ a := (le_abs_self _).trans (hf.trans hd)
    linarith [dist_triangle x v e]
  exact hvis.elim (fun h => hcase h (Or.inl rfl)) (fun h => hcase h (Or.inr rfl))

end Descent

/-- The partner of a seed skipped by an extreme short path must be strictly
outside the chord. Boundary representatives are also excluded quantitatively. -/
lemma partner_outside_tip {F : M.Field J 1} {ε a A : ℝ}
    (x y e : M.Point J root) (D : F.Descent y ε) {b : Fin n}
    (hs : e.height ∈ M.heights e.column b)
    (hw : ∀ s ∈ J, ∀ t ∈ J, |s-t| ≤ a)
    (hz : D.target.column < e.column ∨ b < D.target.column)
    (hxy : 1 ≤ dist x y) (hxe : dist x e ≤ A) (hsmall : (1:ℝ)/50+a+A < 1) :
    y.column < e.column ∨ b < y.column := by
  by_contra h
  have hab : e.column < b := by
    have hadj := M.permitted e.column b e.height hs
    have hne := hadj.ne
    by_contra hh
    push Not at h
    omega
  have hle : e.column ≤ y.column ∧ y.column ≤ b := by push Not at h; exact h
  have hd : dist y e ≤ (1:ℝ)/50+a := by
    by_cases hy : y.column = e.column
    · have := e.dist_to_tip y hs hw (Or.inl hy)
      linarith
    by_cases hy' : y.column = b
    · have := e.dist_to_tip y hs hw (Or.inr hy')
      linarith
    exact D.near_tip e hs hw ⟨lt_of_le_of_ne hle.1 (Ne.symm hy),lt_of_le_of_ne hle.2 hy'⟩ hz
  have ht := dist_triangle x e y
  rw [dist_comm e y] at ht
  linarith

end Field

end PlanarL1.Columns.Model

namespace PlanarL1.ColumnOrder

lemma visits_or_skips_left {n : ℕ} {G : SimpleGraph (Fin n)} {i x y : Fin n}
    (p : G.Walk x y) (hx : i < x) (hy : y < i) :
    i ∈ p.support ∨ JumpsAcross i p := by
  induction p with
  | nil => omega
  | @cons x z y hxz p ih =>
    by_cases hz : z = i
    · left
      exact List.mem_cons_of_mem x (hz ▸ p.start_mem_support)
    by_cases hzi : i < z
    · rcases ih hzi hy with hm | ⟨e,he,hcross⟩
      · left
        simp [hm]
      · right
        exact ⟨e,by simp [he],hcross⟩
    · right
      refine ⟨⟨(x,z),hxz⟩,?_,Or.inr ⟨?_,hx⟩⟩
      · simp
      · change z < i
        omega

/-- The two extremal words cover every intermediate column by a visit or a
strictly skipping dart. No connectedness of the seed set is asserted. -/
lemma extreme_words {n : ℕ} {G : SimpleGraph (Fin n)} {l r c w : Fin n}
    (p : G.Walk c l) (q : G.Walk c r) (hl : l ≤ w) (hr : w ≤ r) :
    (w ∈ p.support ∨ JumpsAcross w p) ∨ (w ∈ q.support ∨ JumpsAcross w q) := by
  rcases lt_trichotomy w c with h | h | h
  · left
    by_cases he : l = w
    · exact Or.inl (he ▸ p.end_mem_support)
    exact visits_or_skips_left p h (lt_of_le_of_ne hl he)
  · left
    left
    exact h ▸ p.start_mem_support
  · right
    by_cases he : w = r
    · exact Or.inl (he ▸ q.end_mem_support)
    exact visits_or_skips q h (lt_of_le_of_ne hr he)

end PlanarL1.ColumnOrder

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

namespace Point

lemma dist_le_trace_length (hJI : J ⊆ I) (c e : M.Point I root) {v : Fin n}
    (p : M.Path J c.column v) {H : ℝ} (he : (e.column,e.height) ∈ p.trace c.height H) :
    dist c e ≤ p.length c.height H := by
  obtain ⟨q,r,hqr⟩ := p.trace_split he
  have hd := c.distance_le e (q.widen hJI)
  rw [Path.length_widen] at hd
  have hn := r.length_nonneg e.height H
  change dist c e ≤ q.length c.height e.height at hd
  linarith

/-- Every actual trace representative is an intrinsic point of the same
larger-band component as the start, not an assumed representative choice. -/
lemma point_on_trace (hJI : J ⊆ I) (c : M.Point I root) {v k : Fin n}
    (p : M.Path J c.column v) {H T : ℝ} (hT : T ∈ J)
    (ht : (k,T) ∈ p.trace c.height H) :
    ∃ e : M.Point I root, e.column = k ∧ e.height = T ∧ dist c e ≤ p.length c.height H := by
  obtain ⟨q,_,_⟩ := p.trace_split ht
  let e : M.Point I root := ⟨k,T,hJI hT,c.reachable.trans (q.widen hJI).word.reachable⟩
  exact ⟨e,rfl,rfl,c.dist_le_trace_length hJI e p ht⟩

end Point

namespace Field

/-- Strict separation of representatives by the chord, with an arbitrary
linear cut outside its first open arc. -/
def TipSeparates (a b x y : Fin n) : Prop :=
  (a < x ∧ x < b ∧ (y < a ∨ b < y)) ∨ (a < y ∧ y < b ∧ (x < a ∨ b < x))

/-- Complement of the main procedure's barrier-drop exclusion. Both endpoint
thresholds are tested, exactly as in pack:barrier and pack:retained-data. -/
def NoLowTip (F : M.Field I 1) (x y : M.Point I root) (J : Set ℝ) (j : ℝ) : Prop :=
  ∀ (e : M.Point I root) (b : Fin n), e.height ∈ J →
    e.height ∈ M.heights e.column b → ¬ Consecutive e.column b →
    TipSeparates e.column b x.column y.column →
    (dist x e ≤ 1 ∨ dist y e ≤ 1) →
    F.eval x-j ≤ F.eval e ∧ F.eval y-j ≤ F.eval e

/-- A single skipping dart of an extreme path puts its seed near the actual
trace. Connected low columns, witness descent and the barrier exclusion are
used here, not replaced by the desired near-path conclusion. -/
lemma skipped_seed_near_trace (F : M.Field I 1) (hI : IsClosed I)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJI : J ⊆ I) {a A j ε : ℝ} (hw : ∀ s ∈ I, ∀ t ∈ I, |s-t| ≤ a)
    (c x y : M.Point I root) (Dx : F.Descent x ε) (Dy : F.Descent y ε)
    (hxS : Dx.target.column ∈ S) (hyS : Dy.target.column ∈ S)
    (hxy : 1 ≤ dist x y) (hcx : dist c x ≤ A) (hA : 2*A ≤ 1)
    (hsmall : (1:ℝ)/50+a+2*A < 1) (hretain : F.NoLowTip x y J j)
    {v : Fin n} (p : M.Path J c.column v) {H : ℝ} (hp : p.length c.height H ≤ A)
    (havoid : ∀ k ∈ p.word.support, k ∉ S) (hskip : ColumnOrder.JumpsAcross x.column p.word) :
    ∃ e : M.Point I root, (e.column,e.height) ∈ p.trace c.height H ∧
      dist x e ≤ j+ε+2*a := by
  obtain ⟨d,hd,hcross⟩ := hskip
  obtain ⟨T,hT,hs,ht₁,ht₂⟩ := p.dart_on_trace c.height H d hd
  have hcase {l r : Fin n} (hlr : l < x.column ∧ x.column < r)
      (hs : T ∈ M.heights l r) (htl : (l,T) ∈ p.trace c.height H)
      (htr : (r,T) ∈ p.trace c.height H) :
      ∃ e : M.Point I root, (e.column,e.height) ∈ p.trace c.height H ∧ dist x e ≤ j+ε+2*a := by
    have hl : l ∉ S := havoid l (p.trace_column htl)
    have hr : r ∉ S := havoid r (p.trace_column htr)
    have hcl : cut < l := lt_of_le_of_ne (hmin l) (fun h => hl (h ▸ hcut))
    have hgap := ColumnOrder.gap_of_chord M.noncrossing hS
      (M.permitted l r T hs) hl hr hcut (Or.inl hcl)
    obtain ⟨e,hecol,heheight,helen⟩ := c.point_on_trace hJI p hT htl
    have hetrace : (e.column,e.height) ∈ p.trace c.height H := by rwa [hecol,heheight]
    have hxe : dist x e ≤ 2*A := by
      have ht := dist_triangle x c e
      rw [dist_comm x c] at ht
      linarith
    have hes : e.height ∈ M.heights e.column r := by rwa [hecol,heheight]
    have hyp : y.column < e.column ∨ r < y.column := partner_outside_tip x y e Dy hes hw
      (by simpa only [hecol] using hgap _ hyS) hxy hxe hsmall
    have hnc : ¬ Consecutive e.column r := by
      rw [hecol]
      exact not_consecutive_of_between hlr (Or.inl hcl)
    have hlow := (hretain e r (heheight ▸ hT) hes hnc
      (Or.inl ⟨by simpa only [hecol] using hlr.1,hlr.2,hyp⟩) (Or.inl (hxe.trans hA))).1
    refine ⟨e,hetrace,Dx.near_tip_of_not_low hI e hes hw ?_ ?_ hlow⟩
    · simpa only [hecol] using hlr
    · simpa only [hecol] using hgap _ hxS
  rcases hcross with hc | hc
  · exact hcase hc hs ht₁ ht₂
  · exact hcase hc (by rwa [M.symm]) ht₂ ht₁

end Field

end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- A visited seed column is vertically near a point of the original trace;
leaving the individual radial cell is allowed throughout. -/
lemma visited_seed_near_trace (hJI : J ⊆ I) {a : ℝ}
    (hw : ∀ s ∈ I, ∀ t ∈ I, |s-t| ≤ a) (c x : M.Point I root)
    (hc : c.height ∈ J) {v : Fin n} (p : M.Path J c.column v) {H : ℝ}
    (hx : x.column ∈ p.word.support) :
    ∃ e : M.Point I root, (e.column,e.height) ∈ p.trace c.height H ∧ dist x e ≤ a := by
  obtain ⟨T,hT,ht⟩ := p.trace_on_column hc hx
  obtain ⟨e,hecol,heheight,_⟩ := c.point_on_trace hJI p hT ht
  refine ⟨e,by rwa [hecol,heheight],?_⟩
  rw [x.dist_same_column e hecol.symm]
  exact hw x.height x.inBand e.height e.inBand

/-- The restricted packing geometry, before the final substitution of fixed
constants. The two extremal paths are selected from the actual center paths.
The low set may be absent from most columns; no doubling or ambient ball
packing hypothesis occurs. -/
theorem restricted_packing {K : Type*} [Fintype K]
    (F : M.Field I 1) (hI : IsClosed I)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJI : J ⊆ I) {a A j ε b : ℝ} (hw : ∀ s ∈ I, ∀ t ∈ I, |s-t| ≤ a)
    (hA₀ : 0 ≤ A) (hA : 2*A ≤ 1) (hsmall : (1:ℝ)/50+a+2*A < 1)
    (hb : 0 < b) (hpad : j+ε+2*a ≤ b/4) (hvisit : a ≤ j+ε+2*a)
    (c : M.Point I root) (hc : c.height ∈ J) (hcS : c.column ∉ S)
    (seed partner : K → M.Point I root)
    (Dx : ∀ w, F.Descent (seed w) ε) (Dy : ∀ w, F.Descent (partner w) ε)
    (hxS : ∀ w, (Dx w).target.column ∈ S) (hyS : ∀ w, (Dy w).target.column ∈ S)
    (hxy : ∀ w, 1 ≤ dist (seed w) (partner w))
    (hretain : ∀ w, F.NoLowTip (seed w) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ A)
    (havoid : ∀ w k, k ∈ (cp w).word.support → k ∉ S)
    (hsep : ∀ w v, w ≠ v → b ≤ dist (seed w) (seed v)) :
    (Fintype.card K : ℝ) ≤ 2+4*A/b := by
  classical
  let endpoint : Option K → M.Point I root := Option.elim' c seed
  let path : ∀ w : Option K, M.Path J c.column (endpoint w).column := fun w =>
    Option.rec (.nil c.column) cp w
  have hlen : ∀ w, (path w).length c.height (endpoint w).height ≤ A := by
    intro w
    cases w with
    | none => simpa only [path,endpoint,Option.elim',Path.length,sub_self,abs_zero] using hA₀
    | some w => exact hp w
  have hav : ∀ w k, k ∈ (path w).word.support → k ∉ S := by
    intro w k hk
    cases w with
    | none =>
      have he : k = c.column := by
        change k ∈ [c.column] at hk
        exact List.mem_singleton.mp hk
      exact he ▸ hcS
    | some w => exact havoid w k hk
  obtain ⟨l,_,hl⟩ := Finset.exists_min_image (Finset.univ : Finset (Option K))
    (fun w => (endpoint w).column) ⟨none,Finset.mem_univ _⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Option K))
    (fun w => (endpoint w).column) ⟨none,Finset.mem_univ _⟩
  let select : Fin 2 → Option K := ![l,r]
  let paths (s : Fin 2) := path (select s)
  have hone (w : K) (v : Option K)
      (hv : (seed w).column ∈ (path v).word.support ∨
        ColumnOrder.JumpsAcross (seed w).column (path v).word) :
      ∃ e : M.Point I root, (e.column,e.height) ∈ (path v).trace c.height (endpoint v).height ∧
        dist (seed w) e ≤ j+ε+2*a := by
    rcases hv with hv | hv
    · obtain ⟨e,he,hnear⟩ := visited_seed_near_trace hJI hw c (seed w) hc (path v) hv
      exact ⟨e,he,hnear.trans hvisit⟩
    · have hcs : dist c (seed w) ≤ A := by
        have hd := c.distance_le (seed w) ((cp w).widen hJI)
        rw [Path.length_widen] at hd
        exact hd.trans (hp w)
      exact F.skipped_seed_near_trace hI hS hcut hmin hJI hw c (seed w) (partner w)
        (Dx w) (Dy w) (hxS w) (hyS w) (hxy w) hcs hA hsmall (hretain w)
        (path v) (hlen v) (hav v) hv
  have hprox : ∀ w : K, ∃ (s : Fin 2) (e : M.Point I root),
      (e.column,e.height) ∈ (paths s).trace c.height (endpoint (select s)).height ∧
        dist (seed w) e ≤ j+ε+2*a := by
    intro w
    have h := ColumnOrder.extreme_words (path l).word (path r).word
      (hl (some w) (Finset.mem_univ _)) (hr (some w) (Finset.mem_univ _))
    rcases h with h | h
    · obtain ⟨e,he,hnear⟩ := hone w l h
      exact ⟨0,e,by simpa only [paths,select,Matrix.cons_val_zero] using he,hnear⟩
    · obtain ⟨e,he,hnear⟩ := hone w r h
      exact ⟨1,e,by simpa only [paths,select,Matrix.cons_val_one,Matrix.cons_val_zero] using he,hnear⟩
  choose side near htrace hnear using hprox
  exact near_two_traces_count hJI hb hA₀ hpad (fun _ => c.column)
    (fun s => (endpoint (select s)).column) paths (fun _ => c.height)
    (fun s => (endpoint (select s)).height) (fun s => hlen (select s))
    seed near side htrace hsep hnear

/-- The source packing number after the restricted geometric argument,
with A=4R and padded distinct cells separated by 0.01g. -/
theorem restricted_packing_number {K : Type*} [Fintype K]
    (F : M.Field I 1) (hI : IsClosed I)
    {S : Set (Fin n)} (hS : (M.link.induce S).Preconnected)
    {cut : Fin n} (hcut : cut ∈ S) (hmin : ∀ v, cut ≤ v)
    (hJI : J ⊆ I) {a R j ε g : ℝ} (hw : ∀ s ∈ I, ∀ t ∈ I, |s-t| ≤ a)
    (hR₀ : 0 ≤ R) (hR : 8*R ≤ 1) (hsmall : (1:ℝ)/50+a+8*R < 1)
    (hg : 0 < g) (hpad : j+ε+2*a ≤ (0.01*g)/4) (hvisit : a ≤ j+ε+2*a)
    (c : M.Point I root) (hc : c.height ∈ J) (hcS : c.column ∉ S)
    (seed partner : K → M.Point I root)
    (Dx : ∀ w, F.Descent (seed w) ε) (Dy : ∀ w, F.Descent (partner w) ε)
    (hxS : ∀ w, (Dx w).target.column ∈ S) (hyS : ∀ w, (Dy w).target.column ∈ S)
    (hxy : ∀ w, 1 ≤ dist (seed w) (partner w))
    (hretain : ∀ w, F.NoLowTip (seed w) (partner w) J j)
    (cp : ∀ w, M.Path J c.column (seed w).column)
    (hp : ∀ w, (cp w).length c.height (seed w).height ≤ 4*R)
    (havoid : ∀ w k, k ∈ (cp w).word.support → k ∉ S)
    (hsep : ∀ w v, w ≠ v → 0.01*g ≤ dist (seed w) (seed v)) :
    Fintype.card K ≤ 2+⌈1600*R/g⌉₊ := by
  have hc := F.restricted_packing hI hS hcut hmin hJI hw (by positivity : 0 ≤ 4*R)
    (by linarith : 2*(4*R) ≤ 1) (by linarith : (1:ℝ)/50+a+2*(4*R) < 1)
    (by positivity : 0 < 0.01*g) hpad hvisit c hc hcS seed partner Dx Dy hxS hyS hxy
    hretain cp hp havoid hsep
  have he : 4*(4*R)/(0.01*g) = 1600*R/g := by ring
  rw [he] at hc
  have hceil := Nat.le_ceil (1600*R/g)
  have : (Fintype.card K : ℝ) ≤ 2+(⌈1600*R/g⌉₊ : ℝ) := by linarith
  exact_mod_cast this

end PlanarL1.Columns.Model.Field


end

end OAI
