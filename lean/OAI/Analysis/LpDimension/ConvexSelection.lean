import OAI.Analysis.LpDimension.Packing

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal
universe u uE uH uJ uX

namespace SubpolynomialLp

section HilbertMatrix
variable {E : Type uE} {H : Type uH} [Fintype E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def hilbertMul (P : Matrix E E ℝ) (x : E → H) (e : E) : H := ∑ f, P e f • x f

lemma hilbertMul_add (P Q : Matrix E E ℝ) (x : E → H) :
    hilbertMul (P+Q) x = hilbertMul P x+hilbertMul Q x := by
  ext e
  simp [hilbertMul, add_smul, Finset.sum_add_distrib]

lemma hilbertMul_smul (a : ℝ) (P : Matrix E E ℝ) (x : E → H) :
    hilbertMul (a • P) x = a • hilbertMul P x := by
  ext e
  simp [hilbertMul, Finset.smul_sum, smul_smul]

lemma hilbertMul_mul (P Q : Matrix E E ℝ) (x : E → H) :
    hilbertMul (P*Q) x = hilbertMul P (hilbertMul Q x) := by
  ext e
  simp only [hilbertMul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma hilbertMul_inner (P : Matrix E E ℝ) (x y : E → H) :
    (∑ e, inner ℝ (hilbertMul P x e) (y e)) = ∑ e, inner ℝ (x e) (hilbertMul P.transpose y e) := by
  simp only [hilbertMul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma hilbertMul_contraction (P : Matrix E E ℝ) (hs : P.IsSymm) (hi : P*P=P)
    (x : E → H) : (∑ e, ‖hilbertMul P x e‖^2) ≤ ∑ e, ‖x e‖^2 := by
  have hp : ∑ e, inner ℝ (hilbertMul P x e) (hilbertMul P x e) =
      ∑ e, inner ℝ (x e) (hilbertMul P x e) := by
    rw [hilbertMul_inner, hs.eq, ← hilbertMul_mul, hi]
  have hnon : 0 ≤ ∑ e, ‖x e-hilbertMul P x e‖^2 := by positivity
  have he : (∑ e, ‖x e-hilbertMul P x e‖^2) =
      (∑ e, ‖x e‖^2) - (∑ e, ‖hilbertMul P x e‖^2) := by
    simp_rw [norm_sub_sq_real]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hp' : ∑ e, ‖hilbertMul P x e‖^2 = ∑ e, inner ℝ (x e) (hilbertMul P x e) := by
      simpa only [real_inner_self_eq_norm_sq] using hp
    linarith
  rw [he] at hnon
  linarith

end HilbertMatrix


lemma weighted_error_to_uniform {E : Type uE} [Fintype E] [Nonempty E]
    {C : Set (E → ℝ)} (hC : Convex ℝ C) (b ε : ℝ) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ m ∈ C, (∑ e, w e * |m e-b|) ≤ ε) :
    ∃ m ∈ C, ∀ e, |m e-b| < 2*ε := by
  classical
  let B : Set (E → ℝ) := Metric.ball (fun _ => b) (2*ε)
  have hB : Convex ℝ B := convex_ball _ _
  have hBc : (fun _ : E => b) ∈ B := Metric.mem_ball_self (by positivity)
  have hBu : ∀ z, z ∈ B ↔ ∀ e, |z e-b| < 2*ε := by
    intro z
    simp only [B, Metric.mem_ball, dist_pi_lt_iff (show 0 < 2*ε by positivity), Real.dist_eq]
  by_contra hnot
  have hd : Disjoint B C := by
    apply Set.disjoint_left.mpr
    intro m hm hmC
    exact hnot ⟨m,hmC,(hBu m).mp hm⟩
  obtain ⟨f,u,hfB,hfC⟩ := geometric_hahn_banach_open hB Metric.isOpen_ball hC hd
  let a : E → ℝ := fun e => f (Pi.single e 1)
  have hrepr (z : E → ℝ) : f z = ∑ e, a e*z e := by
    have he : z = ∑ e : E, z e • Pi.single e (1:ℝ) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [he, map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_smul, smul_eq_mul]
    dsimp [a]
    ring
  let S := ∑ e, |a e|
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcard : 0 < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw0 : ∀ e : E, 0 < (Fintype.card E : ℝ)⁻¹ := fun _ => inv_pos.mpr hcard
  have hsum0 : (∑ _ : E, (Fintype.card E:ℝ)⁻¹) = 1 := by
    simp [hcard.ne']
  obtain ⟨m₀,hm₀,_⟩ := hw (fun _ => (Fintype.card E:ℝ)⁻¹) hw0 hsum0
  have hS : 0 < S := by
    by_contra h
    have hz : S = 0 := le_antisymm (not_lt.mp h) hS0
    have haz (e : E) : a e = 0 := abs_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun e _ => abs_nonneg (a e))).mp hz e (Finset.mem_univ e))
    have hh := hfB _ hBc
    have hj := hfC _ hm₀
    simp only [hrepr, haz, zero_mul, Finset.sum_const_zero] at hh hj
    linarith
  let w : E → ℝ := fun e => 3/4*(|a e|/S)+1/(4*(Fintype.card E))
  have hwpos : ∀ e, 0 < w e := by intro e; dsimp [w]; positivity
  have hwsum : ∑ e, w e = 1 := by
    simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [div_self hS.ne']
    field_simp [hcard.ne']
    ring
  obtain ⟨m,hm,herr⟩ := hw w hwpos hwsum
  have hal (e : E) : |a e| ≤ (4/3)*S*w e := by
    have he : (4/3)*S*w e = |a e|+S/(3*(Fintype.card E)) := by
      dsimp [w]
      field_simp [hS.ne', hcard.ne']
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  have hferr : f m-f (fun _ => b) ≤ (4/3)*S*ε := by
    rw [hrepr, hrepr, ← Finset.sum_sub_distrib]
    calc
      ∑ e, (a e*m e-a e*b) ≤ ∑ e, |a e| *|m e-b| := by
        apply Finset.sum_le_sum
        intro e _
        calc
          _ = a e*(m e-b) := by ring
          _ ≤ |a e*(m e-b)| := le_abs_self _
          _ = _ := abs_mul _ _
      _ ≤ ∑ e, ((4/3)*S*w e)*|m e-b| :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_right (hal e) (abs_nonneg _))
      _ = (4/3)*S*∑ e, w e*|m e-b| := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left herr (by positivity)
  let z : E → ℝ := fun e => b+(3/2)*ε*SignType.sign (a e)
  have hzB : z ∈ B := by
    apply (hBu z).mpr
    intro e
    dsimp [z]
    rcases lt_trichotomy (a e) 0 with h | h | h
    · simp [sign_neg h, abs_of_pos hε]; linarith
    · simp [h]; positivity
    · simp [sign_pos h, abs_of_pos hε]; linarith
  have hzf : f z-f (fun _ => b) = (3/2)*ε*S := by
    rw [hrepr, hrepr, ← Finset.sum_sub_distrib]
    calc
      ∑ e, (a e*z e-a e*b) = ∑ e, (3/2)*ε*|a e| := by
        apply Finset.sum_congr rfl
        intro e _
        dsimp [z]
        rcases lt_trichotomy (a e) 0 with h | h | h
        · rw [sign_neg h, abs_of_neg h]; norm_num; ring
        · simp [h]
        · rw [sign_pos h, abs_of_pos h]; norm_num; ring
      _ = _ := by rw [← Finset.mul_sum]
  have hfz := hfB z hzB
  have hfm := hfC m hm
  nlinarith


/-- Convex separation replaces fixed-point reweighting. -/
lemma convex_cost_selection {X : Type uX} {E : Type uE} [AddCommGroup X] [Module ℝ X]
    [Fintype E] [Nonempty E] {A : Set X} (hA : Convex ℝ A)
    (c : E → X → ℝ) (hc : ∀ e, ConvexOn ℝ A (c e))
    (hcn : ∀ e x, x ∈ A → 0 ≤ c e x) (B : ℝ) (hB : 0 < B)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ x ∈ A, (∑ e, w e*c e x) ≤ B) :
    ∃ x ∈ A, ∀ e, c e x < 2*B := by
  classical
  let C : Set (E → ℝ) := {v | ∃ x ∈ A, ∀ e, c e x ≤ v e}
  have hC : Convex ℝ C := by
    intro v hv z hz a b ha hb hab
    obtain ⟨x,hx,hcx⟩ := hv
    obtain ⟨y,hy,hcy⟩ := hz
    refine ⟨a • x+b • y,hA hx hy ha hb hab,fun e => ?_⟩
    exact ((hc e).2 hx hy ha hb hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hcx e) ha) (mul_le_mul_of_nonneg_left (hcy e) hb))
  have hwt : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ m ∈ C, (∑ e, w e*|m e-(0:ℝ)|) ≤ B := by
    intro w hwp hws
    obtain ⟨x,hx,hxc⟩ := hw w hwp hws
    refine ⟨fun e => c e x,⟨x,hx,fun _ => le_rfl⟩,?_⟩
    simpa only [sub_zero, abs_of_nonneg (hcn _ _ hx)] using hxc
  obtain ⟨v,⟨x,hx,hxv⟩,hve⟩ := weighted_error_to_uniform hC 0 B hB hwt
  refine ⟨x,hx,fun e => (hxv e).trans_lt ?_⟩
  exact (le_abs_self (v e)).trans_lt (by simpa using hve e)


lemma simultaneous_convex_cost_selection {X : Type uX} {E : Type uE} {J : Type uJ}
    [AddCommGroup X] [Module ℝ X] [Fintype E] [Nonempty E] [Fintype J]
    {A : Set X} (hA : Convex ℝ A) (r : E → X → ℝ) (q : J → X → ℝ)
    (hrc : ∀ e, ConvexOn ℝ A (r e)) (hqc : ∀ j, ConvexOn ℝ A (q j))
    (hrn : ∀ e x, x ∈ A → 0 ≤ r e x) (hqn : ∀ j x, x ∈ A → 0 ≤ q j x)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e) = 1 →
      ∃ x ∈ A, (∑ e, w e*r e x) ≤ 2 ∧ ∀ j, q j x ≤ 2) :
    ∃ x ∈ A, (∀ e, r e x < 4) ∧ ∀ j, q j x < 4 := by
  classical
  let c : E ⊕ J → X → ℝ := Sum.elim r q
  have hc : ∀ i, ConvexOn ℝ A (c i) := by intro i; cases i with
    | inl e => exact hrc e
    | inr j => exact hqc j
  have hcn : ∀ i x, x ∈ A → 0 ≤ c i x := by intro i; cases i with
    | inl e => exact hrn e
    | inr j => exact hqn j
  have hwt : ∀ w : E ⊕ J → ℝ, (∀ i, 0 < w i) → (∑ i, w i) = 1 →
      ∃ x ∈ A, (∑ i, w i*c i x) ≤ 2 := by
    intro w hwp hws
    let a := ∑ e, w (Sum.inl e)
    have ha : 0 < a := Finset.sum_pos (fun e _ => hwp (Sum.inl e)) Finset.univ_nonempty
    have hvs : ∑ e, w (Sum.inl e)/a = 1 := by rw [← Finset.sum_div, div_self ha.ne']
    obtain ⟨x,hx,hxr,hxq⟩ := hw (fun e => w (Sum.inl e)/a)
      (fun e => div_pos (hwp _) ha) hvs
    have hxr' : ∑ e, w (Sum.inl e)*r e x ≤ 2*a := by
      have he : ∑ e, w (Sum.inl e)/a*r e x = (∑ e, w (Sum.inl e)*r e x)/a := by
        simp only [div_mul_eq_mul_div, Finset.sum_div]
      rw [he] at hxr
      exact (div_le_iff₀ ha).mp hxr
    have hxq' : ∑ j, w (Sum.inr j)*q j x ≤ 2*(∑ j, w (Sum.inr j)) := by
      calc
        _ ≤ ∑ j, w (Sum.inr j)*2 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hxq j) (hwp _).le)
        _ = _ := by rw [← Finset.sum_mul]; ring
    refine ⟨x,hx,?_⟩
    rw [Fintype.sum_sum_type] at hws ⊢
    dsimp [c]
    change a+(∑ j, w (Sum.inr j))=1 at hws
    linarith
  obtain ⟨x,hx,hxc⟩ := convex_cost_selection hA c hc hcn 2 (by norm_num) hwt
  refine ⟨x,hx,fun e => ?_,fun j => ?_⟩
  · have hh := hxc (Sum.inl e)
    change r e x < 2*2 at hh
    linarith
  · have hh := hxc (Sum.inr j)
    change q j x < 2*2 at hh
    linarith

end SubpolynomialLp

end

end OAI
