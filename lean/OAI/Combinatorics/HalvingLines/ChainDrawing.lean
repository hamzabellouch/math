import OAI.Combinatorics.HalvingLines.Chains

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.flip (S : @System n R k a P) :
    @System n R (n-k) a (fun v => -P v) where
  slope := S.slope
  increasing := S.increasing
  marks b := (S.marks b)ᶜ
  card_marks b := by
    classical
    rw [Finset.card_compl, S.card_marks, Fintype.card_fin]
  separates b := by
    classical
    intro i hi j hj
    have hi' := Finset.mem_compl.mp hi
    have hj' : j ∈ S.marks b := by simpa using hj
    have h := S.separates b j hj' i hi'
    simp only [Sweep.projection, Prod.fst_neg, Prod.snd_neg] at *
    linarith
  distance b := by
    classical
    have he : (S.marks b.castSucc)ᶜ \ (S.marks b.succ)ᶜ = S.gain b := by
      ext u
      simp [System.gain, and_comm]
    rw [he, S.card_gain]

@[simp] lemma System.flip_loss (S : @System n R k a P) (b : Fin R) :
    S.flip.loss b = S.gain b := by
  classical
  ext u
  simp [System.loss, System.gain, System.flip, and_comm]
@[simp] lemma System.flip_gain (S : @System n R k a P) (b : Fin R) :
    S.flip.gain b = S.loss b := by
  classical
  ext u
  simp [System.loss, System.gain, System.flip, and_comm]

lemma System.flip_edge (S : @System n R k a P) (e : Fin n × Fin n) :
    e.swap ∈ S.flip.edges ↔ e ∈ S.edges := by
  rw [S.flip.mem_edges, S.mem_edges]
  simp only [Prod.fst_swap, Prod.snd_swap, System.flip_loss, System.flip_gain, and_comm]

lemma System.flip_vertices (S : @System n R k a P) : S.flip.vertices = S.vertices := by
  classical
  ext u
  simp only [System.vertices, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨e,he,hu⟩ | ⟨e,he,hu⟩)
    · exact Or.inr ⟨e.swap, (S.flip_edge e.swap).mp (by simpa using he), hu⟩
    · exact Or.inl ⟨e.swap, (S.flip_edge e.swap).mp (by simpa using he), hu⟩
  · rintro (⟨e,he,hu⟩ | ⟨e,he,hu⟩)
    · exact Or.inr ⟨e.swap, (S.flip_edge e).mpr he, hu⟩
    · exact Or.inl ⟨e.swap, (S.flip_edge e).mpr he, hu⟩

noncomputable def System.concaveCover (S : @System n R k a P) [NeZero n] [NeZero a] :
    ConcaveCover S.drawing (Fin a × Fin n) where
  owner e := S.flip.convexOwner e.swap
  support e he f hf ho z hz := by
    have he' : e.swap ∈ S.flip.drawing.edges := (S.flip_edge e).mpr he
    have hf' : f.swap ∈ S.flip.drawing.edges := (S.flip_edge f).mpr hf
    have hz' : -z ∈ segment ℝ (-P f.2) (-P f.1) := by
      rw [segment_eq_image] at hz ⊢
      obtain ⟨u,hu,hz⟩ := hz
      refine ⟨1-u, ⟨by linarith only [hu.2], by linarith only [hu.1]⟩, ?_⟩
      rw [← hz]
      module
    have h := S.flip.convexCover.support e.swap he' f.swap hf' ho (-z) hz'
    change height (-P e.2) (-P e.1) (-z.1) ≤ -z.2 at h
    rw [height_neg_reverse _ _ (S.drawing.right e he).ne] at h
    exact neg_le_neg_iff.mp h

lemma System.concaveOwner_mem (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) :
    S.concaveCover.owner e ∈ Finset.univ ×ˢ S.vertices := by
  have h := S.flip.convexOwner_mem ((S.flip_edge e).mpr he)
  rwa [S.flip_vertices] at h

theorem System.crossing_cap (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Position P) (hx : Function.Injective (fun v => (P v).1))
    (hD : S.drawing.NoMultiple) :
    S.drawing.crossings.card ≤ 2 * a^2 * S.vertices.card^2 := by
  have h := S.convexCover.crossing_bound_finset S.concaveCover hP hx hD
    (Finset.univ ×ˢ S.vertices) (Finset.univ ×ˢ S.vertices)
    (fun _ he => S.convexOwner_mem he) (fun _ he => S.concaveOwner_mem he)
  simpa [Finset.card_product, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
variable {n : ℕ} {P : Fin n → Point}

def sortEdge (e : Fin n × Fin n) : Fin n × Fin n :=
  if e.1 < e.2 then e else e.swap

lemma sortEdge_order (e : Fin n × Fin n) (he : e.1 ≠ e.2) :
    (sortEdge e).1 < (sortEdge e).2 := by
  unfold sortEdge
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) he.symm

lemma sortEdge_cases (e : Fin n × Fin n) : sortEdge e = e ∨ sortEdge e = e.swap := by
  unfold sortEdge
  split_ifs <;> simp

lemma sortEdge_coincide {e f : Fin n × Fin n} (he : sortEdge e = sortEdge f) :
    e = f ∨ e = f.swap := by
  rcases sortEdge_cases e with hh | hh <;> rcases sortEdge_cases f with hg | hg <;> rw [hh,hg] at he
  · exact Or.inl he
  · exact Or.inr he
  · exact Or.inr (by simpa using congrArg Prod.swap he)
  · exact Or.inl (Prod.swap_injective he)

lemma Drawing.sortEdge_injective (D : Drawing P) :
    (↑D.edges : Set (Fin n × Fin n)).InjOn (@sortEdge n) := by
  intro e he f hf h
  rcases sortEdge_coincide h with h | h
  · exact h
  · have hx := D.right e he
    have hy := D.right f hf
    rw [h] at hx
    exact False.elim (lt_asymm hx hy)

lemma openSegment_sortEdge (e : Fin n × Fin n) :
    openSegment ℝ (P (sortEdge e).1) (P (sortEdge e).2) =
      openSegment ℝ (P e.1) (P e.2) := by
  rcases sortEdge_cases e with h | h
  · rw [h]
  · rw [h]
    exact openSegment_symm ℝ _ _

lemma segment_sortEdge (e : Fin n × Fin n) :
    segment ℝ (P (sortEdge e).1) (P (sortEdge e).2) =
      segment ℝ (P e.1) (P e.2) := by
  rcases sortEdge_cases e with h | h
  · rw [h]
  · rw [h]
    exact segment_symm ℝ _ _

lemma Drawing.noMultiple_of_generic (D : Drawing P) (hP : Generic P) : D.NoMultiple := by
  intro e he f hf hef g hg hge hgf z hze hzf hzg
  have ho (i : Fin n × Fin n) (hi : i ∈ D.edges) : (sortEdge i).1 < (sortEdge i).2 :=
    sortEdge_order i (fun h => (D.right i hi).ne (congrArg (fun v => (P v).1) h))
  have hne {i j : Fin n × Fin n} (hi : i ∈ D.edges) (hj : j ∈ D.edges) (hn : i ≠ j) :
      sortEdge i ≠ sortEdge j := fun h => hn (D.sortEdge_injective hi hj h)
  apply hP.2.2.2 _ _ _ _ _ _ (ho e he) (ho f hf) (ho g hg)
    (hne he hf hef) (hne hg he hge) (hne hg hf hgf) z
  · rwa [openSegment_sortEdge]
  · rwa [openSegment_sortEdge]
  · rwa [segment_sortEdge]

lemma Generic.position (hP : Generic P) : Position P := hP.1
lemma Generic.x_injective (hP : Generic P) : Function.Injective (fun v => (P v).1) := by
  intro i j hij
  by_contra hn
  exact hP.2.1 i j hn hij

end PlanarHalving.PlaneGraph

namespace PlanarHalving.PlaneGraph
variable {V : Type*} [Fintype V] {P : V → Point}

noncomputable def Drawing.restrictEdges (D : Drawing P) (E : Finset (V × V)) : Drawing P := by
  classical
  exact {
    vertices := D.vertices
    edges := D.edges ∩ E
    right := fun e he => D.right e (Finset.mem_inter.mp he).1
    ends := fun e he => D.ends e (Finset.mem_inter.mp he).1 }

lemma Drawing.restrict_crossings (D : Drawing P) (E : Finset (V × V)) :
    (D.restrictEdges E).crossings ⊆ D.crossings := by
  classical
  intro w hw
  simp only [Drawing.crossings, Drawing.restrictEdges, Finset.mem_filter,
    Finset.mem_product, Finset.mem_inter] at hw ⊢
  exact ⟨⟨hw.1.1.1,hw.1.2.1⟩,hw.2⟩

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertices_le (S : @System n R k a P) : S.vertices.card ≤ n := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

theorem System.localized_crossing (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) (F : Finset (Fin n)) (hF : F ⊆ S.vertices) :
    ((S.edges.filter fun e => e.1 ∈ F).card : ℝ)^3 ≤
      4608 * (a : ℝ)^2 * F.card * (S.vertices.card : ℝ)^3 +
        13824 * (S.vertices.card : ℝ)^3 := by
  classical
  let D := S.drawing.restrictEdges (S.edges.filter fun e => e.1 ∈ F)
  have hv : D.vertices = S.vertices := rfl
  have he : D.edges = S.edges.filter (fun e => e.1 ∈ F) := by
    ext e
    simp [D, Drawing.restrictEdges, System.drawing]
  have hc := D.designated_crossing hP.1 (PlaneGraph.Generic.x_injective hP) F hF (by
    intro e he'
    rw [he] at he'
    exact Or.inl (Finset.mem_filter.mp he').2)
  rw [he,hv] at hc
  have hcr : (D.crossings.card : ℝ) ≤ 2 * (a : ℝ)^2 * (S.vertices.card : ℝ)^2 := by
    exact_mod_cast (Finset.card_le_card (S.drawing.restrict_crossings _)).trans
      (S.crossing_cap hP.1 (PlaneGraph.Generic.x_injective hP) (S.drawing.noMultiple_of_generic hP))
  apply hc.trans
  calc 2304 * (F.card : ℝ) * S.vertices.card * D.crossings.card +
        13824 * (S.vertices.card : ℝ)^3 ≤
      2304 * (F.card : ℝ) * S.vertices.card * (2 * (a : ℝ)^2 * (S.vertices.card : ℝ)^2) +
        13824 * (S.vertices.card : ℝ)^3 := by gcongr
    _ = _ := by ring

theorem System.cubed_bound (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) :
    (R : ℝ)^3 * (a : ℝ)^4 ≤ 18432 * (n : ℝ)^4 := by
  classical
  have hc := S.localized_crossing hP S.vertices (by rfl)
  have he : S.edges.filter (fun e => e.1 ∈ S.vertices) = S.edges := by
    exact Finset.filter_eq_self.mpr (fun e he => (S.edge_ends he).1)
  rw [he, S.card_edges] at hc
  push_cast at hc
  have hs : (S.vertices.card : ℝ) ≤ n := by exact_mod_cast S.vertices_le
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast (NeZero.one_le : 1 ≤ a)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (NeZero.one_le : 1 ≤ n)
  have hs₁ : 4608 * (a : ℝ)^2 * S.vertices.card * (S.vertices.card : ℝ)^3 ≤
      4608 * (a : ℝ)^2 * (n : ℝ)^4 := by
    calc _ ≤ 4608 * (a : ℝ)^2 * n * (n : ℝ)^3 := by gcongr
      _ = _ := by ring
  have hs₂ : 13824 * (S.vertices.card : ℝ)^3 ≤ 13824 * (a : ℝ)^2 * (n : ℝ)^4 := by
    calc _ ≤ 13824 * (n : ℝ)^3 := by gcongr
      _ = 13824 * (1 : ℝ)^2 * (1 * (n : ℝ)^3) := by ring
      _ ≤ 13824 * (a : ℝ)^2 * (n * (n : ℝ)^3) := by gcongr
      _ = _ := by ring
  have hh : (a : ℝ)^2 * ((R : ℝ)^3 * (a : ℝ)^4) ≤
      (a : ℝ)^2 * (18432 * (n : ℝ)^4) := by
    nlinarith only [hc, hs₁, hs₂]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (a : ℝ)^2)).mp hh

end PlanarHalving.Batches
namespace PlanarHalving.PlaneGraph
lemma height_of_mem_segment {p q z : Point} (hx : p.1 ≠ q.1)
    (hz : z ∈ segment ℝ p q) : z.2 = height p q z.1 := by
  rw [segment_eq_image] at hz
  obtain ⟨t,_,rfl⟩ := hz
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  unfold height slope
  field_simp
  ring
end PlanarHalving.PlaneGraph

namespace PlanarHalving.RankCoordinates
open Set

noncomputable def envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => m i*x+c i)

lemma le_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (i : ι) (x : ℝ) : m i*x+c i ≤ envelope m c x :=
  Finset.le_sup' (fun j => m j*x+c j) (Finset.mem_univ i)

lemma envelope_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (x y : ℝ) (h : ∀ i, m i*x+c i ≤ y) : envelope m c x ≤ y :=
  Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i)

lemma envelope_attains {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (x : ℝ) : ∃ i, envelope m c x = m i*x+c i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => m i*x+c i) Finset.univ_nonempty
  exact ⟨i, le_antisymm (envelope_le m c x _ (fun j => hi j (Finset.mem_univ j))) (le_envelope m c i x)⟩

lemma continuous_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) : Continuous (envelope m c) := by
  have hh : Continuous (Finset.univ.sup' Finset.univ_nonempty (fun i => fun x : ℝ => m i*x+c i)) :=
    Continuous.finset_sup' Finset.univ_nonempty (fun _ _ => by fun_prop)
  convert hh using 1
  funext x
  simp only [envelope, Finset.sup'_apply]

lemma convexOn_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) : ConvexOn ℝ Set.univ (envelope m c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply envelope_le
  intro i
  have h₁ := mul_le_mul_of_nonneg_left (le_envelope m c i x) ha
  have h₂ := mul_le_mul_of_nonneg_left (le_envelope m c i y) hb
  calc
    m i * (a*x+b*y)+c i = a*(m i*x+c i)+b*(m i*y+c i) := by
      have hh := congrArg (fun t => t * c i) hab
      nlinarith only [hh]
    _ ≤ _ := add_le_add h₁ h₂

lemma envelope_slopes {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) {l u : ℝ} (hm : ∀ i, l ≤ m i ∧ m i ≤ u)
    {x y : ℝ} (hxy : x ≤ y) :
    l*(y-x) ≤ envelope m c y - envelope m c x ∧
    envelope m c y - envelope m c x ≤ u*(y-x) := by
  obtain ⟨i,hi⟩ := envelope_attains m c x
  obtain ⟨j,hj⟩ := envelope_attains m c y
  have h₁ := le_envelope m c i y
  have h₂ := le_envelope m c j x
  have h₃ := mul_le_mul_of_nonneg_right (hm i).1 (sub_nonneg.mpr hxy)
  have h₄ := mul_le_mul_of_nonneg_right (hm j).2 (sub_nonneg.mpr hxy)
  constructor
  · rw [hi]
    linarith only [h₁,h₃]
  · rw [hj]
    linarith only [h₂,h₄]

end PlanarHalving.RankCoordinates

namespace PlanarHalving.Batches
open PlaneGraph RankCoordinates
variable {R : ℕ}

lemma ConvexPath.lower_ray (C : ConvexPath R) {l : ℝ}
    (hl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ → l ≤ slope (C.point b.castSucc) (C.point b.succ))
    (c : Fin (R+1)) :
    (C.point 0).2 + ( (C.point c).1 - (C.point 0).1)*l ≤ (C.point c).2 := by
  have h := fin_between_le (f := fun r => Sweep.projection l (C.point r)) 0 c (Fin.zero_le c) (by
    intro b _ _
    rcases C.right b with he | he
    · rw [he]
    · have hn : C.point b.castSucc ≠ C.point b.succ := fun h => he.ne (congrArg Prod.fst h)
      have hp := projection_step (C.point b.castSucc) (C.point b.succ) (t := l) he.ne
      have hprod := mul_nonneg (sub_nonneg.mpr he.le) (sub_nonneg.mpr (hl b hn))
      linarith only [hp,hprod])
  unfold Sweep.projection at h
  linarith only [h]

lemma ConvexPath.upper_ray (C : ConvexPath R) {u : ℝ}
    (hu : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ → slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (c : Fin (R+1)) :
    (C.point (Fin.last R)).2 + ((C.point c).1 - (C.point (Fin.last R)).1)*u ≤ (C.point c).2 := by
  have h := fin_between_le (f := fun r => -Sweep.projection u (C.point r)) c (Fin.last R) (Fin.le_last c) (by
    intro b _ _
    rcases C.right b with he | he
    · rw [he]
    · have hn : C.point b.castSucc ≠ C.point b.succ := fun h => he.ne (congrArg Prod.fst h)
      have hp := projection_step (C.point b.castSucc) (C.point b.succ) (t := u) he.ne
      have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr he.le) (sub_nonpos.mpr (hu b hn))
      linarith only [hp,hprod])
  unfold Sweep.projection at h
  linarith only [h]

noncomputable def ConvexPath.extensionSlopes (C : ConvexPath R) (l u : ℝ) : Fin R ⊕ Bool → ℝ
  | .inl b => if C.point b.castSucc = C.point b.succ then l else slope (C.point b.castSucc) (C.point b.succ)
  | .inr false => l
  | .inr true => u

noncomputable def ConvexPath.extensionIntercepts (C : ConvexPath R) (l u : ℝ) : Fin R ⊕ Bool → ℝ
  | .inl b => if C.point b.castSucc = C.point b.succ then (C.point 0).2 - l*(C.point 0).1
      else (C.point b.castSucc).2 - slope (C.point b.castSucc) (C.point b.succ)*(C.point b.castSucc).1
  | .inr false => (C.point 0).2 - l*(C.point 0).1
  | .inr true => (C.point (Fin.last R)).2 - u*(C.point (Fin.last R)).1

noncomputable def ConvexPath.extension (C : ConvexPath R) (l u : ℝ) : ℝ → ℝ :=
  envelope (C.extensionSlopes l u) (C.extensionIntercepts l u)

lemma ConvexPath.extension_slopes (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u) :
    ∀ i, l ≤ C.extensionSlopes l u i ∧ C.extensionSlopes l u i ≤ u := by
  intro i
  cases i with
  | inl b =>
    by_cases hb : C.point b.castSucc = C.point b.succ
    · simp only [ConvexPath.extensionSlopes, ite_eq_left hb]
      exact ⟨le_rfl,hlu⟩
    · simpa only [ConvexPath.extensionSlopes, ite_eq_right hb] using hsl b hb
  | inr b => cases b <;> simp only [ConvexPath.extensionSlopes] <;> exact ⟨by order, by order⟩

lemma ConvexPath.extension_below_vertex (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (c : Fin (R+1)) : C.extension l u (C.point c).1 ≤ (C.point c).2 := by
  apply envelope_le
  intro i
  have hl := C.lower_ray (fun b hb => (hsl b hb).1) c
  have hu := C.upper_ray (fun b hb => (hsl b hb).2) c
  cases i with
  | inl b =>
    by_cases hb : C.point b.castSucc = C.point b.succ
    · simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts, ite_eq_left hb]
      linarith only [hl]
    · simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts, ite_eq_right hb]
      have hh := C.support_vertex b hb c
      unfold height at hh
      linarith only [hh]
  | inr b => cases b <;> simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] <;> linarith only [hl,hu]

lemma ConvexPath.extension_edge (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (b : Fin R) (hb : C.point b.castSucc ≠ C.point b.succ) {z : Point}
    (hz : z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ)) :
    C.extension l u z.1 = z.2 := by
  apply le_antisymm
  · rw [segment_eq_image] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have hc := convexOn_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u)
    have hh := hc.2 (Set.mem_univ (C.point b.castSucc).1) (Set.mem_univ (C.point b.succ).1)
      (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    have h₀ := mul_le_mul_of_nonneg_left (C.extension_below_vertex hsl b.castSucc) (sub_nonneg.mpr ht.2)
    have h₁ := mul_le_mul_of_nonneg_left (C.extension_below_vertex hsl b.succ) ht.1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
    exact hh.trans (add_le_add h₀ h₁)
  · have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inl b) z.1
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts, ite_eq_right hb] at hh
    have hz' := height_of_mem_segment (C.right b |>.resolve_left hb).ne hz
    unfold height at hz'
    change z.2 ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) z.1
    linarith only [hh,hz']

end PlanarHalving.Batches

end OAI
