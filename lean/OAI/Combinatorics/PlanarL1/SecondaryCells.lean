import OAI.Combinatorics.PlanarL1.MainCells

namespace OAI

section

namespace PlanarL1.Columns.Model.SecondaryCell
open scoped NNReal
open Metric

variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))

noncomputable def seedDistance (x : M.Point J root) : ℝ := infDist x (S : Set (M.Point J root))

lemma seedDistance_nonneg (x : M.Point J root) : 0 ≤ seedDistance S x := infDist_nonneg

lemma seedDistance_lipschitz : LipschitzWith 1 (seedDistance S) := lipschitz_infDist_pt _

lemma seedDistance_seed {w : M.Point J root} (hw : w ∈ S) : seedDistance S w = 0 :=
  infDist_zero_of_mem hw

lemma seedDistance_attained (hS : S.Nonempty) (x : M.Point J root) :
    ∃ w ∈ S, seedDistance S x = dist x w := by
  exact S.finite_toSet.isCompact.exists_infDist_eq_dist (by simpa using hS) x

noncomputable def input (x : M.Point J root) : ℝ := (9/10:ℝ)*seedDistance S x

lemma input_lipschitz (hζ : R.ζ = (1:ℝ)/10) : R.InputLip (input S) := by
  intro x y
  have h := (seedDistance_lipschitz S).dist_le_mul x y
  rw [NNReal.coe_one,one_mul] at h
  rw [input,input,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 9/10),hζ]
  rw [Real.dist_eq] at h
  nlinarith

noncomputable def approx (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) : ℝ :=
  (R.pasted (input S) α x).value

noncomputable def shallow (pc radius : ℝ) (α : Point.RadialTree.Noise (n := n))
    (x : M.Point J root) : ℝ := pc+radius/20-approx R S α x

lemma approx_accuracy (hζ : R.ζ = (1:ℝ)/10) {radius : ℝ} (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (x : M.Point J root) :
    |approx R S α x-(9/10:ℝ)*seedDistance S x| ≤ radius/1000 := by
  have h := R.pasted_accuracy (input_lipschitz R S hζ) hα x
  rw [hδ] at h
  change |approx R S α x-(9/10:ℝ)*seedDistance S x| ≤ _ at h
  have hp := R.delta_pos
  rw [hδ] at hp
  linarith

lemma shallow_lipschitz (pc radius : ℝ) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) : LipschitzWith 1 (shallow R S pc radius α) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [shallow,approx,dist_sub_left] using (R.pasted_lipschitz (input S) hα).dist_le_mul x y

lemma shallow_boundary (hζ : R.ζ = (1:ℝ)/10) {radius pc : ℝ} (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {x : M.Point J root}
    (hx : seedDistance S x = radius) : shallow R S pc radius α x ≤ pc-(849/1000:ℝ)*radius := by
  have h := (abs_le.mp (approx_accuracy R S hζ hδ hα x)).1
  dsimp only [shallow]
  rw [hx] at h
  linarith

lemma shallow_cap (hζ : R.ζ = (1:ℝ)/10) {radius pc : ℝ} (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (x : M.Point J root) :
    shallow R S pc radius α x ≤ pc+(51/1000:ℝ)*radius := by
  have h := (abs_le.mp (approx_accuracy R S hζ hδ hα x)).1
  dsimp only [shallow]
  linarith [seedDistance_nonneg S x]

lemma shallow_seed (hζ : R.ζ = (1:ℝ)/10) {radius pc : ℝ} (hr : 0 < radius)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) {w : M.Point J root} (hw : w ∈ S) {p : ℝ}
    (hp : |p-pc| ≤ (60/1000000:ℝ)*radius) :
    p+radius/25 < shallow R S pc radius α w := by
  have h := (abs_le.mp (approx_accuracy R S hζ hδ hα w)).2
  rw [seedDistance_seed S hw,mul_zero,sub_zero] at h
  have hpc := (abs_le.mp hp).2
  dsimp only [shallow]
  linarith

end PlanarL1.Columns.Model.SecondaryCell


end

section

namespace PlanarL1.Columns.Model.Point
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
lemma height_lipschitz : LipschitzWith 1 (fun x : M.Point J root => x.height) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,NNReal.coe_one,one_mul]
  exact x.height_change_le y
end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.SecondaryCell
open Set Metric
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (S : Finset (M.Point J root)) (radius : ℝ)

/-- The literal closed union of radius-R seed balls, on each vertical column. -/
def domain (i : Fin n) : Set ℝ :=
  (fun x : M.Point J root => x.height) ''
    {x | x.column = i ∧ seedDistance S x ≤ radius}

lemma mem_domain {i : Fin n} {H : ℝ} : H ∈ domain S radius i ↔
    ∃ x : M.Point J root, x.column = i ∧ x.height = H ∧ seedDistance S x ≤ radius := by
  constructor
  · rintro ⟨x,⟨hi,hd⟩,hH⟩
    exact ⟨x,hi,hH,hd⟩
  · rintro ⟨x,hi,hH,hd⟩
    exact ⟨x,⟨hi,hd⟩,hH⟩

lemma compact_domain (hJ : IsCompact J) (i : Fin n) : IsCompact (domain S radius i) := by
  have hc : IsCompact {x : M.Point J root | x.column = i} := by
    simpa only [mem_singleton_iff] using Point.fullColumns_compact (M := M) (root := root) hJ {i}
  have hd : IsClosed {x : M.Point J root | seedDistance S x ≤ radius} :=
    isClosed_le (seedDistance_lipschitz S).continuous continuous_const
  exact (hc.inter_right hd).image Point.height_lipschitz.continuous

noncomputable def point (i : Fin n) (H : ℝ) (h : H ∈ domain S radius i) : M.Point J root :=
  ((mem_domain S radius).mp h).choose

lemma point_column {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    (point S radius i H h).column = i := ((mem_domain S radius).mp h).choose_spec.1
lemma point_height {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    (point S radius i H h).height = H := ((mem_domain S radius).mp h).choose_spec.2.1
lemma point_distance {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    seedDistance S (point S radius i H h) ≤ radius := ((mem_domain S radius).mp h).choose_spec.2.2

lemma inBand_of_mem {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) : H ∈ J := by
  rw [← point_height S radius h]
  exact (point S radius i H h).inBand

lemma equal_radius_or_endpoint (hJ : IsCompact J) (lo a : ℝ) (_ha : 0 < a)
    (hband : J = Icc lo (lo+a)) {i : Fin n} {H : ℝ} (h : H ∈ frontier (domain S radius i)) :
    ∃ hd : H ∈ domain S radius i,
      seedDistance S (point S radius i H hd) = radius ∨ H = lo ∨ H = lo+a := by
  have hd : H ∈ domain S radius i := (compact_domain S radius hJ i).isClosed.frontier_subset h
  refine ⟨hd,?_⟩
  let x := point S radius i H hd
  by_cases hs : seedDistance S x = radius
  · exact Or.inl hs
  right
  by_cases hl : H = lo
  · exact Or.inl hl
  right
  by_contra hr
  have hH : H ∈ Icc lo (lo+a) := hband ▸ inBand_of_mem S radius hd
  have hlo : lo < H := lt_of_le_of_ne hH.1 (Ne.symm hl)
  have hhi : H < lo+a := lt_of_le_of_ne hH.2 hr
  have hdist : seedDistance S x < radius := lt_of_le_of_ne (point_distance S radius hd) hs
  let ε := min (H-lo) (min (lo+a-H) (radius-seedDistance S x)) / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεl : ε < H-lo := by
    have hh := min_le_left (H-lo) (min (lo+a-H) (radius-seedDistance S x))
    dsimp only [ε]
    linarith
  have hεh : ε < lo+a-H := by
    have hh := (min_le_right (H-lo) (min (lo+a-H) (radius-seedDistance S x))).trans (min_le_left _ _)
    dsimp only [ε]
    linarith
  have hεd : ε < radius-seedDistance S x := by
    have hh := (min_le_right (H-lo) (min (lo+a-H) (radius-seedDistance S x))).trans (min_le_right _ _)
    dsimp only [ε]
    linarith
  have hb : Metric.ball H ε ⊆ domain S radius i := by
    intro T hT
    have ht := abs_lt.mp (by simpa only [Metric.mem_ball,Real.dist_eq] using hT : |T-H| < ε)
    have hTJ : T ∈ J := by rw [hband]; constructor <;> linarith
    let y := x.withHeight T hTJ
    have hy : dist y x = |T-H| := by
      rw [y.dist_same_column x rfl]
      change |T-x.height| = |T-H|
      rw [point_height S radius hd]
    have hbnd := (seedDistance_lipschitz S).dist_le_mul y x
    rw [Real.dist_eq,NNReal.coe_one,one_mul,hy] at hbnd
    have hby := (abs_le.mp hbnd).2
    apply (mem_domain S radius).mpr
    exact ⟨y,point_column S radius hd,rfl,by linarith [(by
      simpa only [Metric.mem_ball,Real.dist_eq] using hT : |T-H| < ε)]⟩
  have hin : H ∈ interior (domain S radius i) :=
    mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨ε,hε,hb⟩)
  exact h.2 hin

/-- The seed-ball domain is saturated under the actual quotient switches. -/
lemma switch_mem {i j : Fin n} {H : ℝ} (hs : H ∈ M.heights i j)
    (hi : H ∈ domain S radius i) : H ∈ domain S radius j := by
  let x := point S radius i H hi
  have hHJ := inBand_of_mem S radius hi
  have hadj : (M.activeGraph J).Adj i j := ⟨H,hHJ,hs⟩
  have hxi := point_column S radius hi
  have hxH := point_height S radius hi
  let y : M.Point J root := ⟨j,H,hHJ,(hxi ▸ x.reachable).trans hadj.reachable⟩
  have hd : dist x y = 0 := by
    apply le_antisymm _ dist_nonneg
    have hiCol : x.column = i := hxi
    have hiHeight : x.height = H := hxH
    have hjCol : y.column = j := rfl
    have hjHeight : y.height = H := rfl
    have h := x.dist_le_switch y hHJ (by rw [hiCol,hjCol]; exact hs)
    simpa only [hiHeight,hjHeight,sub_self,abs_zero,add_zero] using h
  have hf := (seedDistance_lipschitz S).dist_le_mul x y
  rw [hd,mul_zero] at hf
  have he : seedDistance S x = seedDistance S y := dist_le_zero.mp hf
  exact (mem_domain S radius).mpr ⟨y,rfl,rfl,he ▸ point_distance S radius hi⟩

end PlanarL1.Columns.Model.SecondaryCell



namespace PlanarL1.Columns.Model.SecondaryCell
open Set MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))
variable (old L : M.Point J root → ℝ) (ordinary : Bool)

noncomputable def spatial (pc radius αo : ℝ) (α : Point.RadialTree.Noise (n := n))
    (x : M.Point J root) : ℝ :=
  if ordinary then min (shallow R S pc radius α x) (Clipping.orderedBranch pc radius αo L x)
  else shallow R S pc radius α x

noncomputable def replacement (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) : ℝ :=
  max (old x) (min (spatial R S L ordinary pc radius αo α x)
    (Clipping.heightShield lo R.a pc αh x.height))

noncomputable def replacementConstant : ℝ≥0 := max 5 ⟨3/(9*R.a/100),by positivity [R.width_pos]⟩

lemma spatial_lipschitz (pc radius αo : ℝ) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) (hL : LipschitzWith 1 L) :
    LipschitzWith 4 (spatial R S L ordinary pc radius αo α) := by
  have hT := (shallow_lipschitz R S pc radius hα).weaken (by norm_num : (1:ℝ≥0) ≤ 4)
  have hO : LipschitzWith 4 (Clipping.orderedBranch pc radius αo L) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hL.dist_le_mul x y
    rw [Real.dist_eq,NNReal.coe_one,one_mul] at h
    change dist _ _ ≤ (4:ℝ)*dist x y
    rw [Real.dist_eq]
    change |(pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo)| ≤ _
    rw [show (pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo) =
      4*(L x-L y) by ring, abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
    linarith
  cases ordinary
  · convert hT using 1; funext x; simp only [spatial,Bool.false_eq_true,ite_false]
  · convert hT.min hO using 1
    · exact (max_self _).symm
    · funext x; simp only [spatial,ite_true]

lemma replacement_lipschitz (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) :
    LipschitzWith (replacementConstant R) (replacement R S old L ordinary pc radius αo αh lo α) := by
  apply Clipping.clip_lipschitz
  · exact hOld.weaken (le_max_left _ _)
  · exact (spatial_lipschitz R S L ordinary pc radius αo hα hL).weaken
      ((by norm_num : (4:ℝ≥0) ≤ 5).trans (le_max_left _ _))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (Clipping.heightShield_lipschitz lo pc αh R.width_pos).dist_le_mul x.height y.height
    have hheight := x.height_change_le y
    change |x.height-y.height| ≤ dist x y at hheight
    change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
    change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at h
    rw [Real.dist_eq x.height y.height] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hheight (by positivity [R.width_pos])).trans
      (mul_le_mul_of_nonneg_right (le_max_right (5:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma replacement_near (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    {pc radius : ℝ} (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    {x : M.Point J root} (hx : seedDistance S x ≤ radius) :
    |old x-pc| ≤ 5*radius+(60/1000000:ℝ)*radius := by
  obtain ⟨w,hw,hd⟩ := seedDistance_attained S hS x
  have ho := hOld.dist_le_mul x w
  rw [Real.dist_eq] at ho
  have hs := hseed w hw
  have hh := abs_sub_le (old x) (old w) pc
  change |old x-old w| ≤ 5*dist x w at ho
  linarith

lemma spatial_boundary (hS : S.Nonempty) (hζ : R.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    {x : M.Point J root} (hx : seedDistance S x = radius) :
    spatial R S L ordinary pc radius αo α x ≤ old x-(199/1000:ℝ)*radius := by
  have hT := shallow_boundary R S hζ hδ hα hx (pc := pc)
  cases ordinary with
  | false =>
    simp only [spatial,Bool.false_eq_true,ite_false]
    obtain ⟨w,hw,hd⟩ := seedDistance_attained S hS x
    have ha := hadmit rfl w hw x (by rw [dist_comm,← hd,hx])
    linarith
  | true =>
    simp only [spatial,ite_true]
    exact Clipping.ordinary_boundary_margin hr hαo (hord rfl x) hT

lemma replacement_boundary (hS : S.Nonempty) (hζ : R.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (αh lo : ℝ) {x : M.Point J root} (hx : seedDistance S x = radius) :
    replacement R S old L ordinary pc radius αo αh lo α x = old x := by
  apply max_eq_left
  have h := spatial_boundary R S old L ordinary hS hζ hr hαo hδ hα hord hadmit hx
  exact (min_le_left _ _).trans (by linarith)

lemma replacement_endpoint (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    {pc radius αo αh lo : ℝ} (hr : radius ≤ (1:ℝ)/100) (hαh : αh ≤ radius/1000)
    (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    (α : Point.RadialTree.Noise (n := n)) {x : M.Point J root}
    (hx : seedDistance S x ≤ radius) (he : x.height = lo ∨ x.height = lo+R.a) :
    replacement R S old L ordinary pc radius αo αh lo α x = old x := by
  apply max_eq_left
  have h := (abs_le.mp (replacement_near S old hS hOld hseed hx)).1
  have hh : Clipping.heightShield lo R.a pc αh x.height = pc-1+αh := by
    rcases he with he | he
    · exact Clipping.heightShield_left (by rw [he])
    · exact Clipping.heightShield_right (by rw [he])
  apply (min_le_right _ _).trans
  rw [hh]
  linarith

lemma scaled_replacement_constant (ha : R.a ≤ 1) :
    (R.a/1000000) * (replacementConstant R : ℝ) ≤ 1 := by
  change (R.a/1000000) * max 5 (3/(9*R.a/100)) ≤ 1
  rw [mul_max_of_nonneg (5:ℝ) (3/(9*R.a/100)) (by positivity [R.width_pos])]
  apply max_le
  · linarith
  · have hpos : 0 < 9*R.a/100 := by positivity [R.width_pos]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [R.width_pos]

lemma point_dist {radius : ℝ} {i : Fin n} {H T : ℝ}
    (hH : H ∈ domain S radius i) (hT : T ∈ domain S radius i) :
    dist (point S radius i H hH) (point S radius i T hT) = |H-T| := by
  rw [Point.dist_same_column _ _ (by rw [point_column S radius hH,point_column S radius hT])]
  rw [point_height S radius hH,point_height S radius hT]

lemma point_dist_switch {radius : ℝ} {i j : Fin n} {H : ℝ}
    (hH : H ∈ domain S radius i) (hT : H ∈ domain S radius j) (hs : H ∈ M.heights i j) :
    dist (point S radius i H hH) (point S radius j H hT) = 0 := by
  apply le_antisymm _ dist_nonneg
  have h := (point S radius i H hH).dist_le_switch (point S radius j H hT)
    (inBand_of_mem S radius hH) (by rw [point_column S radius hH,point_column S radius hT]; exact hs)
  simpa only [point_height S radius hH,point_height S radius hT,sub_self,abs_zero,add_zero] using h

noncomputable def converted (pc radius αo αh lo c η κ : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (i : Fin n) (H : ℝ) : ℝ :=
  if h : H ∈ domain S radius i then
    κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α (point S radius i H h)) else 0

lemma converted_on (pc radius αo αh lo c η κ : ℝ)
    (α : Point.RadialTree.Noise (n := n)) {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    converted R S old L ordinary pc radius αo αh lo c η κ α i H =
      κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α (point S radius i H h)) := by
  simp only [converted,dite_eq_left h]

lemma converted_lipschitz (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo c η κ : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1) (i : Fin n) :
    LipschitzOnWith 1 (converted R S old L ordinary pc radius αo αh lo c η κ α i) (domain S radius i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro H hH T hT
  rw [converted_on R S old L ordinary pc radius αo αh lo c η κ α hH,
    converted_on R S old L ordinary pc radius αo αh lo c η κ α hT]
  let x := point S radius i H hH
  let y := point S radius i T hT
  have h := (replacement_lipschitz R S old L ordinary hOld hL pc radius αo αh lo hα).dist_le_mul x y
  rw [point_dist S hH hT,Real.dist_eq] at h
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  change |κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α x)-
    κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α y)| ≤ |H-T|
  rw [show κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α x)-
    κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α y) =
    κ*η*(replacement R S old L ordinary pc radius αo αh lo α x-
      replacement R S old L ordinary pc radius αo αh lo α y) by ring,
    abs_mul,abs_mul,abs_of_nonneg hκ,hη,mul_one]
  calc
    _ ≤ κ*((replacementConstant R : ℝ)*|H-T|) := mul_le_mul_of_nonneg_left h hκ
    _ = (κ*(replacementConstant R : ℝ))*|H-T| := by ring
    _ ≤ 1*|H-T| := mul_le_mul_of_nonneg_right hκK (abs_nonneg _)
    _ = _ := one_mul _

/-- Literal secondary clipping on the actual closed seed-ball union, in both
ordinary and admitted ordered orientations, is an invariant-preserving patch. -/
noncomputable def patch {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : SetSystem M Ω μ) (Z : Threshold.Variables Ω μ)
    (hJ : IsCompact J) (lo : ℝ) (hband : J = Icc lo (lo+R.a))
    (hS : S.Nonempty) (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (hζ : R.ζ = (1:ℝ)/10) (pc radius αo αh c η κ : ℝ)
    (hr : 0 ≤ radius) (hrsmall : radius ≤ (1:ℝ)/100) (hαo : αo ≤ radius/1000)
    (hαh : αh ≤ radius/1000) (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1)
    (hchart : ∀ ω i H (h : H ∈ domain S radius i),
      Threshold.active Z H (κ*(c+η*old (point S radius i H h))) ω ↔ (A.activity ω).active i H) :
    SetPatch A := by
  have hclosed := fun i => (compact_domain S radius hJ i).isClosed
  apply Threshold.chartPatch A Z (domain S radius) hclosed
    (converted R S old L ordinary pc radius αo αh lo c η κ α)
    (converted_lipschitz R S old L ordinary hOld hL pc radius αo αh lo c η κ hα hη hκ hκK)
  · intro ω i H hH
    obtain ⟨hd,he⟩ := equal_radius_or_endpoint S radius hJ lo R.a R.width_pos hband hH
    rw [converted_on R S old L ordinary pc radius αo αh lo c η κ α hd]
    have heq : replacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd) =
        old (point S radius i H hd) := by
      rcases he with he | he
      · exact replacement_boundary R S old L ordinary hS hζ hr hαo hδ hα hord hadmit αh lo he
      · exact replacement_endpoint R S old L ordinary hS hOld hrsmall hαh hseed α
          (point_distance S radius hd) (by rw [point_height S radius hd]; exact he)
    rw [heq]
    exact hchart ω i H hd
  · intro i j H hs hi hj
    rw [converted_on R S old L ordinary pc radius αo αh lo c η κ α hi,
      converted_on R S old L ordinary pc radius αo αh lo c η κ α hj]
    have h := (replacement_lipschitz R S old L ordinary hOld hL pc radius αo αh lo hα).dist_le_mul
      (point S radius i H hi) (point S radius j H hj)
    rw [point_dist_switch S hi hj hs,mul_zero] at h
    rw [dist_le_zero.mp h]
  · intro ω i j H hs hi hj
    exact (hj (switch_mem S radius hs hi)).elim

lemma replacement_seed (hζ : R.ζ = (1:ℝ)/10) {pc radius αo αh lo : ℝ}
    (hr : 0 < radius) (hrsmall : radius ≤ (1:ℝ)/100) (hαo : 0 ≤ αo) (hαh : 0 ≤ αh)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {w : M.Point J root} (hw : w ∈ S) (hp : |old w-pc| ≤ (60/1000000:ℝ)*radius)
    (hL : ordinary = true → |L w-pc| ≤ (10/1000000:ℝ)*radius)
    (hl : lo+9*R.a/100 ≤ w.height) (hh : w.height ≤ lo+R.a-9*R.a/100) :
    old w+radius/25 < replacement R S old L ordinary pc radius αo αh lo α w := by
  apply lt_of_lt_of_le _ (le_max_right _ _)
  apply lt_min
  · have hT := shallow_seed R S hζ hr hδ hα hw hp
    cases ordinary with
    | false => exact hT
    | true => exact lt_min hT (Clipping.orderedBranch_seed hr hαo (hL rfl) hp)
  · rw [Clipping.heightShield_plateau R.width_pos hl hh]
    have h := (abs_le.mp hp).2
    linarith

lemma replacement_movement (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    (hζ : R.ζ = (1:ℝ)/10) {pc radius αo αh lo : ℝ} (hr : 0 ≤ radius)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    {x : M.Point J root} (hx : seedDistance S x ≤ radius) :
    |replacement R S old L ordinary pc radius αo αh lo α x-old x| ≤ (51/10:ℝ)*radius := by
  have hold : old x ≤ replacement R S old L ordinary pc radius αo αh lo α x := le_max_left _ _
  rw [abs_of_nonneg (sub_nonneg.mpr hold)]
  apply sub_le_iff_le_add.mpr
  apply max_le
  · linarith
  · apply (min_le_left _ _).trans
    have hsp : spatial R S L ordinary pc radius αo α x ≤ shallow R S pc radius α x := by
      cases ordinary
      · exact le_rfl
      · exact min_le_left _ _
    have hcap := shallow_cap R S hζ hδ hα x (pc := pc)
    have hnear := (abs_le.mp (replacement_near S old hS hOld hseed hx)).1
    linarith

end PlanarL1.Columns.Model.SecondaryCell




end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)

noncomputable def namedReplacement (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) : M.Point J root → NamedValue :=
  secondaryNamed (fun x => ⟨(R.pasted (input S) α x).name,shallow R S pc radius α x⟩)
    old (Clipping.orderedBranch pc radius αo L)
    (fun x => Clipping.heightShield lo R.a pc αh x.height) ordinary

lemma namedReplacement_value (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α x).value =
      replacement R S old L ordinary pc radius αo αh lo α x := by
  rw [namedReplacement,secondaryNamed_value]
  rfl

noncomputable def localAtom {k : ℕ} (A : R.Node k)
    (pc radius αo αh lo : ℝ) (α : Point.RadialTree.Noise (n := n)) : ℕ → M.Point J root → ℝ :=
  secondaryAtom (fun i x => pc+radius/20-(R.listedAtom (input S) α A R.lookback i x).value)
    old (Clipping.orderedBranch pc radius αo L)
    (fun x => Clipping.heightShield lo R.a pc αh x.height)

lemma orderedBranch_lipschitz (hL : LipschitzWith 1 L) (pc radius αo : ℝ) :
    LipschitzWith 4 (Clipping.orderedBranch pc radius αo L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hL.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  change |(pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo)| ≤ 4*dist x y
  rw [show (pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo) =
    4*(L x-L y) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  linarith

lemma shield_lipschitz (pc αh lo : ℝ) :
    LipschitzWith (replacementConstant R)
      (fun x : M.Point J root => Clipping.heightShield lo R.a pc αh x.height) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (Clipping.heightShield_lipschitz lo pc αh R.width_pos).dist_le_mul x.height y.height
  have hh := x.height_change_le y
  change |x.height-y.height| ≤ dist x y at hh
  change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
  change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at h
  rw [Real.dist_eq x.height y.height] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hh (by positivity [R.width_pos])).trans
    (mul_le_mul_of_nonneg_right (le_max_right (5:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma localAtom_lipschitz (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    {k : ℕ} (A : R.Node k) (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (i : ℕ) :
    LipschitzWith (replacementConstant R) (localAtom R S old L A pc radius αo αh lo α i) := by
  apply secondaryAtom_lipschitz
  · intro i
    apply LipschitzWith.weaken _ (show (1:ℝ≥0) ≤ replacementConstant R from
      (by norm_num : (1:ℝ≥0) ≤ 5).trans (le_max_left _ _))
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_left] using (R.listedAtom_lipschitz (input S) α A R.lookback i).dist_le_mul x y
  · exact hOld.weaken (le_max_left _ _)
  · exact (orderedBranch_lipschitz L hL pc radius αo).weaken
      ((by norm_num : (4:ℝ≥0) ≤ 5).trans (le_max_left _ _))
  · exact shield_lipschitz R pc αh lo

lemma localAtomPair_probability_lt {k : ℕ} (A : R.Node k) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ secondaryNames (R.recentNames A R.lookback))
    (hj : j ∈ secondaryNames (R.recentNames A R.lookback)) (hij : i < j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      |localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) i x-
       localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  have hp : 0 ≤ (2*t+R.q/m)/R.q := by positivity [R.q_pos]
  have hq : 0 ≤ (2*t+B/m)/B := by positivity
  by_cases hj1 : j=1
  · have hi0 : i=0 := by omega
    subst i; subst j
    apply FiniteRandom.prob_prod_bound
    intro ω
    apply FiniteRandom.prob_prod_bound
    intro r
    let c := Clipping.heightShield lo R.a pc 0 x.height-old x
    apply (FiniteRandom.prob_mono (fun s h => ?_)).trans
      ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
    have he : c+B/m*s.val =
        localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 1 x-
        localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 0 x := by
      simp only [localAtom,secondaryAtom, reduceCtorEq,ite_true,ite_false,c,Clipping.heightShield]
      ring
    rw [he,abs_sub_comm]
    exact h
  · by_cases hi1 : i=1
    · subst i
      have hj0 : j ≠ 0 := by omega
      apply FiniteRandom.prob_prod_bound
      intro ω
      apply FiniteRandom.prob_prod_bound
      intro r
      let c := Clipping.heightShield lo R.a pc 0 x.height-
        localAtom R S old L A pc radius (B/m*r.val) 0 lo (R.gridNoise cap m ω) j x
      apply (FiniteRandom.prob_mono (fun s h => ?_)).trans
        ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
      have he : c+B/m*s.val =
          localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 1 x-
          localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) j x := by
        simp only [localAtom,secondaryAtom, reduceCtorEq,ite_true,ite_false,ite_eq_right hj0,ite_eq_right hj1,c,Clipping.heightShield]
        split_ifs <;> ring
      rwa [he]
    · by_cases hj2 : j=2
      · have hi0 : i=0 := by omega
        subst i; subst j
        apply FiniteRandom.prob_prod_bound
        intro ω
        apply FiniteRandom.prob_prod_bound_left
        intro s
        let c := Clipping.orderedBranch pc radius 0 L x-old x
        apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
          ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
        have he : c+B/m*r.val =
            localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 2 x-
            localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 0 x := by
          simp only [localAtom,secondaryAtom, reduceCtorEq, show (2:ℕ) ≠ 1 by decide,ite_true,ite_false,c,Clipping.orderedBranch]
          ring
        rw [he,abs_sub_comm]
        exact h
      · have hj3 : 3 ≤ j := by omega
        have hj0 : j ≠ 0 := by omega
        have hjS : j-3 ∈ R.recentNames A R.lookback := by
          rcases mem_secondaryNames.mp hj with h | h | h | h
          · omega
          · exact (hj1 h).elim
          · exact (hj2 h).elim
          · exact h.2
        by_cases hi2 : i=2
        · subst i
          apply FiniteRandom.prob_prod_bound
          intro ω
          apply FiniteRandom.prob_prod_bound_left
          intro s
          let c := Clipping.orderedBranch pc radius 0 L x-
            (pc+radius/20-(R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (j-3) x).value)
          apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
            ((FiniteRandom.grid_probability m hm hB ht c).trans (le_add_of_nonneg_left hp))
          have he : c+B/m*r.val =
              localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 2 x-
              localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) j x := by
            simp only [localAtom,secondaryAtom, reduceCtorEq, show (2:ℕ) ≠ 1 by decide,ite_true,ite_false,ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2,c,Clipping.orderedBranch]
            ring
          rwa [he]
        · by_cases hi0 : i=0
          · subst i
            apply FiniteRandom.prob_prod_bound_left
            intro rs
            apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
              ((R.listedConstant_probability (input S) A R.lookback (j-3) hjS x
                (pc+radius/20-old x) cap m hk hm ht).trans (le_add_of_nonneg_right hq))
            have he : (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (j-3) x).value-
                (pc+radius/20-old x) =
              localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) 0 x-
              localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) j x := by
              simp only [localAtom,secondaryAtom, reduceCtorEq,ite_true,ite_false,ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2]
              ring
            rwa [he]
          · have hiS : i-3 ∈ R.recentNames A R.lookback := by
              rcases mem_secondaryNames.mp hi with h | h | h | h
              · exact (hi0 h).elim
              · exact (hi1 h).elim
              · exact (hi2 h).elim
              · exact h.2
            have hi3 : 3 ≤ i := by omega
            have hneq : i-3 ≠ j-3 := by omega
            apply FiniteRandom.prob_prod_bound_left
            intro rs
            apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
              ((R.listedPair_probability (input S) A R.lookback (i-3) (j-3) hiS hjS hneq x cap m hk hm ht).trans
                (le_add_of_nonneg_right hq))
            have he :
                localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) i x-
                localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) j x =
                (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (j-3) x).value-
                (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (i-3) x).value := by
              simp only [localAtom,secondaryAtom,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,ite_eq_right hj0,ite_eq_right hj1,ite_eq_right hj2]
              ring
            rw [he,abs_sub_comm] at h
            exact h


lemma localAtomPair_probability {k : ℕ} (A : R.Node k) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i j : ℕ) (hi : i ∈ secondaryNames (R.recentNames A R.lookback))
    (hj : j ∈ secondaryNames (R.recentNames A R.lookback)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      |localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) i x-
       localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) j x| ≤ t) ≤
      (2*t+R.q/m)/R.q + (2*t+B/m)/B := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact localAtomPair_probability_lt R S old L A x pc radius lo B hB cap m hk hm i j hi hj hij ht
  · simpa only [abs_sub_comm] using
      localAtomPair_probability_lt R S old L A x pc radius lo B hB cap m hk hm j i hj hi hji ht

/-- Literal secondary proposal with all spatial, ordered and height branches.
The common atom list is determined before the fresh clipping parameters. -/
lemma namedReplacement_probability (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (hζ : R.ζ = (1:ℝ)/10) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius)
    (m : ℕ) (hm : 0 < m) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) R.depthCap m × (Fin (m+1) × Fin (m+1)) =>
      ∃ z : M.Point J root, dist x z ≤ ρ ∧
        (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo
          (R.gridNoise R.depthCap m ω.1) z).name ≠
        (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo
          (R.gridNoise R.depthCap m ω.1) x).name) ≤
      (6*(R.lookback+1)+3 : ℕ)^2 *
        ((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q +
          (4*(replacementConstant R : ℝ)*ρ+B/m)/B) := by
  classical
  obtain ⟨k,A,hlo,heq⟩ := R.common_formula x hρ hs
  have hk : k < R.depthCap :=
    (R.depth_le_layerDepth x (hlo x (by simpa using hρ))).trans_lt (R.layerDepth_lt_cap x)
  have hlist (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × (Fin (m+1) × Fin (m+1)))
      (z : M.Point J root) (hz : dist x z ≤ ρ) :
      (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo
        (R.gridNoise R.depthCap m ω.1) z).name ∈ secondaryNames (R.recentNames A R.lookback) ∧
      (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo
        (R.gridNoise R.depthCap m ω.1) z).value =
      localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise R.depthCap m ω.1)
        (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo
          (R.gridNoise R.depthCap m ω.1) z).name z := by
    let α := R.gridNoise R.depthCap m ω.1
    have hα := R.gridNoise_bounds R.depthCap m hm ω.1
    have hp := input_lipschitz R S hζ
    have ha : |(R.formula (input S) α k A z).value-input S z| ≤ 6*R.δ := by
      rw [← heq (input S) α hα z hz]
      exact R.pasted_accuracy hp hα z
    have hn : (R.pasted (input S) α z).name ∈ R.recentNames A R.lookback := by
      rw [heq (input S) α hα z hz]
      exact R.formula_name_recent hp hα k A z (hlo z hz) ha
    have hv : R.pasted (input S) α z = R.listedAtom (input S) α A R.lookback (R.pasted (input S) α z).name z := by
      rw [heq (input S) α hα z hz]
      exact R.formula_eq_listed hp hα k A z (hlo z hz) ha
    apply secondaryNamed_list
      (fun z => ⟨(R.pasted (input S) α z).name,pc+radius/20-(R.pasted (input S) α z).value⟩)
      (fun i z => pc+radius/20-(R.listedAtom (input S) α A R.lookback i z).value)
      old (Clipping.orderedBranch pc radius (B/m*ω.2.1.val) L)
      (fun z => Clipping.heightShield lo R.a pc (B/m*ω.2.2.val) z.height)
      ordinary (R.recentNames A R.lookback) z hn
    exact congrArg (fun Z : NamedValue => pc+radius/20-Z.value) hv
  let b : ℝ := (4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q +
      (4*(replacementConstant R : ℝ)*ρ+B/m)/B
  have hb : 0 ≤ b := by dsimp [b]; positivity [R.q_pos]
  have hF (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × (Fin (m+1) × Fin (m+1))) :
      LipschitzWith (replacementConstant R)
        (fun z => (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo
          (R.gridNoise R.depthCap m ω.1) z).value) := by
    simp only [namedReplacement_value]
    exact replacement_lipschitz R S old L ordinary hOld hL _ _ _ _ _
      (R.gridNoise_bounds R.depthCap m hm ω.1)
  have hA (ω : Point.RadialTree.GridSample (n := n) R.depthCap m × (Fin (m+1) × Fin (m+1))) (i : ℕ) :
      LipschitzWith (replacementConstant R)
        (localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise R.depthCap m ω.1) i) :=
    localAtom_lipschitz R S old L hOld hL A _ _ _ _ _ _ i
  have hp := selection_probability _ _ (secondaryNames (R.recentNames A R.lookback)) hF
    (fun ω i _ => hA ω i) x hρ hb hlist
    (fun i hi j hj hij => by
      simpa only [show 2*(2*(replacementConstant R : ℝ)*ρ) = 4*(replacementConstant R : ℝ)*ρ by ring] using
        localAtomPair_probability R S old L A x pc radius lo B hB R.depthCap m hk hm i j hi hj hij
          (t := 2*(replacementConstant R : ℝ)*ρ) (by positivity))
  refine hp.trans ?_
  apply mul_le_mul_of_nonneg_right _ hb
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast (secondaryNames_card (R.recentNames A R.lookback)).trans
    (Nat.add_le_add_right (R.recentNames_card A R.lookback) 3)

end PlanarL1.Columns.Model.SecondaryCell



end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)

include R in
/-- When a small ball meets the complement of the seed-ball domain, every
inside point is close to its actual distance frontier. -/
lemma near_seed_frontier (x y z : M.Point J root) {ρ radius : ℝ}
    (hy : dist x y ≤ ρ) (hz : dist x z ≤ ρ)
    (hout : radius ≤ seedDistance S y) (hin : seedDistance S z ≤ radius) :
    ∃ w : M.Point J root, seedDistance S w=radius ∧ dist z w ≤ 2*ρ := by
  obtain ⟨w,hw,hd⟩ := Point.intermediate_between (seedDistance S) (seedDistance_lipschitz S)
    R.closed_band R.interval_band z y hin hout
  refine ⟨w,hw,?_⟩
  have hzy : dist z y ≤ 2*ρ := by linarith [dist_triangle z x y,dist_comm z x]
  linarith [dist_nonneg (x := w) (y := y)]

/-- The .199R spatial margin defeats the total 4+5 scalar slopes. Consequently
an entire ball touching outside is unchanged, without paying the much larger
height-shield Lipschitz constant. -/
lemma replacement_boundary_ball (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    (hL : LipschitzWith 1 L) (hζ : R.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (αh lo : ℝ) (x y : M.Point J root) {ρ : ℝ}
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*radius)
    (hy : dist x y ≤ ρ) (hout : radius ≤ seedDistance S y)
    (z : M.Point J root) (hz : dist x z ≤ ρ) (hin : seedDistance S z ≤ radius) :
    replacement R S old L ordinary pc radius αo αh lo α z = old z := by
  obtain ⟨w,hw,hd⟩ := near_seed_frontier R S x y z hy hz hout hin
  have hb := spatial_boundary R S old L ordinary hS hζ hr hαo hδ hα hord hadmit hw
  have hs := (spatial_lipschitz R S L ordinary pc radius αo hα hL).dist_le_mul z w
  have ho := hOld.dist_le_mul z w
  rw [Real.dist_eq] at hs ho
  change |spatial R S L ordinary pc radius αo α z-spatial R S L ordinary pc radius αo α w| ≤ 4*dist z w at hs
  change |old z-old w| ≤ 5*dist z w at ho
  have hsz := (abs_le.mp hs).2
  have hoz := (abs_le.mp ho).1
  apply max_eq_left
  exact (min_le_left _ _).trans (by linarith)

end PlanarL1.Columns.Model.SecondaryCell



end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ)

lemma localAtomConstant_probability {k : ℕ} (A : R.Node k) (x : M.Point J root)
    (pc radius lo B : ℝ) (hB : 0 < B) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    (i : ℕ) (hi : i ∈ secondaryNames (R.recentNames A R.lookback)) (hi0 : i ≠ 0)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      |localAtom R S old L A pc radius (B/m*ω.2.1.val) (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) i x-c| ≤ t) ≤
      (2*t+R.q/m)/R.q+(2*t+B/m)/B := by
  have hp : 0 ≤ (2*t+R.q/m)/R.q := by positivity [R.q_pos]
  have hq : 0 ≤ (2*t+B/m)/B := by positivity
  by_cases hi1 : i=1
  · subst i
    apply FiniteRandom.prob_prod_bound
    intro ω
    apply FiniteRandom.prob_prod_bound
    intro r
    let d := Clipping.heightShield lo R.a pc 0 x.height-c
    apply (FiniteRandom.prob_mono (fun s h => ?_)).trans
      ((FiniteRandom.grid_probability m hm hB ht d).trans (le_add_of_nonneg_left hp))
    have he : d+B/m*s.val =
        localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 1 x-c := by
      simp only [localAtom,secondaryAtom,reduceCtorEq,ite_true,ite_false,d,Clipping.heightShield]
      ring
    rwa [he]
  · by_cases hi2 : i=2
    · subst i
      apply FiniteRandom.prob_prod_bound
      intro ω
      apply FiniteRandom.prob_prod_bound_left
      intro s
      let d := Clipping.orderedBranch pc radius 0 L x-c
      apply (FiniteRandom.prob_mono (fun r h => ?_)).trans
        ((FiniteRandom.grid_probability m hm hB ht d).trans (le_add_of_nonneg_left hp))
      have he : d+B/m*r.val =
          localAtom R S old L A pc radius (B/m*r.val) (B/m*s.val) lo (R.gridNoise cap m ω) 2 x-c := by
        simp only [localAtom,secondaryAtom,reduceCtorEq,show (2:ℕ) ≠ 1 by decide,
          ite_true,ite_false,d,Clipping.orderedBranch]
        ring
      rwa [he]
    · have hiS : i-3 ∈ R.recentNames A R.lookback := by
        rcases mem_secondaryNames.mp hi with h | h | h | h
        · exact (hi0 h).elim
        · exact (hi1 h).elim
        · exact (hi2 h).elim
        · exact h.2
      apply FiniteRandom.prob_prod_bound_left
      intro rs
      apply (FiniteRandom.prob_mono (fun ω h => ?_)).trans
        ((R.listedConstant_probability (input S) A R.lookback (i-3) hiS x
          (pc+radius/20-c) cap m hk hm ht).trans (le_add_of_nonneg_right hq))
      have he : (R.listedAtom (input S) (R.gridNoise cap m ω) A R.lookback (i-3) x).value-(pc+radius/20-c) =
          -(localAtom R S old L A pc radius (B/m*rs.1.val) (B/m*rs.2.val) lo (R.gridNoise cap m ω) i x-c) := by
        simp only [localAtom,secondaryAtom,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2]
        ring
      rwa [he,abs_neg]

/-- All seed groups may use the same geometric radial hierarchy. The hierarchy
and the whole local list are chosen before their independent samples. -/
lemma namedReplacement_local_list (hζ : R.ζ = (1:ℝ)/10)
    {k : ℕ} (A : R.Node k) (x : M.Point J root) {ρ : ℝ}
    (hlo : ∀ z : M.Point J root, dist x z ≤ ρ →
      (k:ℝ)*R.δ ≤ dist R.base (z.withHeight R.base.height R.base.inBand))
    (heq : ∀ (p : M.Point J root → ℝ) (α : Point.RadialTree.Noise (n := n)),
      R.NoiseBounds α → ∀ z : M.Point J root, dist x z ≤ ρ →
        R.pasted p α z = R.formula p α k A z)
    (ordinary : Bool) (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (hα : R.NoiseBounds α)
    (z : M.Point J root) (hz : dist x z ≤ ρ) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α z).name ∈
        secondaryNames (R.recentNames A R.lookback) ∧
      (namedReplacement R S old L ordinary pc radius αo αh lo α z).value =
        localAtom R S old L A pc radius αo αh lo α
          (namedReplacement R S old L ordinary pc radius αo αh lo α z).name z := by
  have hp := input_lipschitz R S hζ
  have ha : |(R.formula (input S) α k A z).value-input S z| ≤ 6*R.δ := by
    rw [← heq (input S) α hα z hz]
    exact R.pasted_accuracy hp hα z
  have hn : (R.pasted (input S) α z).name ∈ R.recentNames A R.lookback := by
    rw [heq (input S) α hα z hz]
    exact R.formula_name_recent hp hα k A z (hlo z hz) ha
  have hv : R.pasted (input S) α z = R.listedAtom (input S) α A R.lookback (R.pasted (input S) α z).name z := by
    rw [heq (input S) α hα z hz]
    exact R.formula_eq_listed hp hα k A z (hlo z hz) ha
  apply secondaryNamed_list
    (fun z => ⟨(R.pasted (input S) α z).name,pc+radius/20-(R.pasted (input S) α z).value⟩)
    (fun i z => pc+radius/20-(R.listedAtom (input S) α A R.lookback i z).value)
    old (Clipping.orderedBranch pc radius αo L)
    (fun z => Clipping.heightShield lo R.a pc αh z.height)
    ordinary (R.recentNames A R.lookback) z hn
  exact congrArg (fun Z : NamedValue => pc+radius/20-Z.value) hv


noncomputable def simultaneousNamed {groups : ℕ}
    (seeds : Fin groups → Finset (M.Point J root)) (old : M.Point J root → ℝ)
    (supports : Fin groups → M.Point J root → ℝ) (ordinary : Bool)
    (pc : Fin groups → ℝ) (radius lo B : ℝ) (cap m : ℕ)
    (ω : Fin groups → Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1))) :=
  familySelection old (fun g => namedReplacement R (seeds g) old (supports g) ordinary
    (pc g) radius (B/m*(ω g).2.1.val) (B/m*(ω g).2.2.val) lo (R.gridNoise cap m (ω g).1))

lemma sampledReplacement_lipschitz (ordinary : Bool)
    (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius lo B : ℝ) (cap m : ℕ) (hm : 0 < m)
    (ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1))) :
    LipschitzWith (replacementConstant R) (fun z =>
      (namedReplacement R S old L ordinary pc radius (B/m*ω.2.1.val)
        (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1) z).value) := by
  simp only [namedReplacement_value]
  exact replacement_lipschitz R S old L ordinary hOld hL _ _ _ _ _
    (R.gridNoise_bounds cap m hm ω.1)

lemma simultaneousNamed_local_probability {groups k : ℕ} (cap : ℕ)
    (seeds : Fin groups → Finset (M.Point J root)) (old : M.Point J root → ℝ)
    (supports : Fin groups → M.Point J root → ℝ) (ordinary : Bool)
    (hOld : LipschitzWith 5 old) (hL : ∀ g, LipschitzWith 1 (supports g))
    (hζ : R.ζ = (1:ℝ)/10) (pc : Fin groups → ℝ) (radius lo B : ℝ) (hB : 0 < B)
    (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (A : R.Node k) (hk : k < cap)
    (hlo : ∀ z : M.Point J root, dist x z ≤ ρ →
      (k:ℝ)*R.δ ≤ dist R.base (z.withHeight R.base.height R.base.inBand))
    (heq : ∀ (p : M.Point J root → ℝ) (α : Point.RadialTree.Noise (n := n)),
      R.NoiseBounds α → ∀ z : M.Point J root, dist x z ≤ ρ →
        R.pasted p α z = R.formula p α k A z)
    (m : ℕ) (hm : 0 < m) :
    FiniteRandom.prob (fun ω : Fin groups →
      Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) =>
      ∃ z : M.Point J root, dist x z ≤ ρ ∧
        (simultaneousNamed R seeds old supports ordinary pc radius lo B cap m ω z).name ≠
          (simultaneousNamed R seeds old supports ordinary pc radius lo B cap m ω x).name) ≤
      (1+groups*(6*(R.lookback+1)+3) : ℕ)^2 *
        ((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q+
          (4*(replacementConstant R : ℝ)*ρ+B/m)/B) := by
  classical
  let F := fun (g : Fin groups)
    (ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1))) =>
    namedReplacement R (seeds g) old (supports g) ordinary (pc g) radius (B/m*ω.2.1.val)
      (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1)
  let atom := fun (g : Fin groups)
    (ω : Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1))) =>
    localAtom R (seeds g) old (supports g) A (pc g) radius (B/m*ω.2.1.val)
      (B/m*ω.2.2.val) lo (R.gridNoise cap m ω.1)
  let names : Fin groups → Finset ℕ := fun _ => secondaryNames (R.recentNames A R.lookback)
  have hF g ω : LipschitzWith (replacementConstant R) (fun z => (F g ω z).value) :=
    sampledReplacement_lipschitz R (seeds g) old (supports g) ordinary hOld (hL g)
      (pc g) radius lo B cap m hm ω
  have hA g ω i : LipschitzWith (replacementConstant R) (atom g ω i) :=
    localAtom_lipschitz R (seeds g) old (supports g) hOld (hL g) A _ _ _ _ _ _ i
  have h0 g ω z : atom g ω 0 z=old z := by simp [atom,localAtom,secondaryAtom]
  have hcard g : (names g).card ≤ 6*(R.lookback+1)+3 :=
    (secondaryNames_card _).trans (Nat.add_le_add_right (R.recentNames_card A R.lookback) 3)
  have hlist g ω z (hz : dist x z ≤ ρ) : (F g ω z).name ∈ names g ∧
      (F g ω z).value=atom g ω (F g ω z).name z :=
    namedReplacement_local_list R (seeds g) old (supports g) hζ A x hlo heq ordinary _ _ _ _ _ _
      (R.gridNoise_bounds cap m hm ω.1) z hz
  have ht : 0 ≤ 2*(replacementConstant R : ℝ)*ρ := by positivity
  change FiniteRandom.prob (fun ω : Fin groups →
    Point.RadialTree.GridSample (n := n) cap m × (Fin (m+1) × Fin (m+1)) => ∃ z, dist x z ≤ ρ ∧
    (familySelection old (fun g => F g (ω g)) z).name ≠
      (familySelection old (fun g => F g (ω g)) x).name) ≤ _
  apply familySelection_probability (K := replacementConstant R) old F atom names (hOld.weaken (le_max_left _ _))
    hF hA h0 hcard x hρ (by positivity [R.q_pos]) hlist
  · intro g i hi j hj hij
    simpa only [atom, show 2*(2*(replacementConstant R : ℝ)*ρ)=4*(replacementConstant R : ℝ)*ρ by ring] using
      localAtomPair_probability R (seeds g) old (supports g) A x (pc g) radius lo B hB cap m hk hm
        i j hi hj hij ht
  · intro g i hi hi0 c
    simpa only [atom, show 2*(2*(replacementConstant R : ℝ)*ρ)=4*(replacementConstant R : ℝ)*ρ by ring] using
      localAtomConstant_probability R (seeds g) old (supports g) A x (pc g) radius lo B hB cap m hk hm
        i hi hi0 c ht

/-- The actual simultaneous secondary finite maximum has a local name bound
independent of graph size once seed packing bounds the number of groups. -/
theorem simultaneousNamed_probability {groups : ℕ}
    (seeds : Fin groups → Finset (M.Point J root)) (old : M.Point J root → ℝ)
    (supports : Fin groups → M.Point J root → ℝ) (ordinary : Bool)
    (hOld : LipschitzWith 5 old) (hL : ∀ g, LipschitzWith 1 (supports g))
    (hζ : R.ζ = (1:ℝ)/10) (pc : Fin groups → ℝ) (radius lo B : ℝ) (hB : 0 < B)
    (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius)
    (m : ℕ) (hm : 0 < m) :
    FiniteRandom.prob (fun ω : Fin groups →
      Point.RadialTree.GridSample (n := n) R.depthCap m × (Fin (m+1) × Fin (m+1)) =>
      ∃ z : M.Point J root, dist x z ≤ ρ ∧
        (simultaneousNamed R seeds old supports ordinary pc radius lo B R.depthCap m ω z).name ≠
          (simultaneousNamed R seeds old supports ordinary pc radius lo B R.depthCap m ω x).name) ≤
      (1+groups*(6*(R.lookback+1)+3) : ℕ)^2 *
        ((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q+
          (4*(replacementConstant R : ℝ)*ρ+B/m)/B) := by
  obtain ⟨k,A,hlo,heq⟩ := R.common_formula x hρ hs
  have hk : k < R.depthCap :=
    (R.depth_le_layerDepth x (hlo x (by simpa using hρ))).trans_lt (R.layerDepth_lt_cap x)
  exact simultaneousNamed_local_probability R R.depthCap seeds old supports ordinary hOld hL hζ pc radius lo B hB
    x hρ A hk hlo heq m hm

end PlanarL1.Columns.Model.SecondaryCell



end

end OAI
