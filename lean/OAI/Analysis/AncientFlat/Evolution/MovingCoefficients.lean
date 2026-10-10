import OAI.Analysis.AncientFlat.Evolution.MovingBounds
import OAI.Analysis.AncientFlat.Kernel.SymbolJets

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff BoundedContinuousFunction
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma SymbolBounds.moving_coefficients {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) :
    ∃ α β C L B : ℝ, 0<α ∧ 0≤C ∧ 0≤L ∧ 0≤B ∧
    ∃ A : C(ℝ,V →ᵇ Icc α β), ∃ b : C(ℝ,V →ᵇ ℂ),
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (A t x).val=Real.exp (-t)/16*Af (Real.exp (t/4) • x)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, b t x=1/2+(Bf (Real.exp (t/4) • x) : ℂ)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ‖b t‖≤B) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1, ∀ x z : V,
        |(A t x).val-(A r z).val|≤L*(‖x-z‖+|t-r|)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x z : V, ‖b t x-b t z‖≤L*‖x-z‖) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ContDiff ℝ ∞ (fun x => (A t x).val)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ n : ℕ, n≤2 → ∀ x,
        ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖≤C) := by
  classical
  obtain ⟨κ,hκ,hκA⟩ := h.2.1
  obtain ⟨M,hM,hMA,hMB⟩ := h.absolute_bound
  obtain ⟨L,hL,hLj⟩ := h.first_bounds
  obtain ⟨C,hC,hCj⟩ := h.moving_A_two_jets
  let α : ℝ := Real.exp (-1)/16*κ
  let J : ℝ := M+Real.exp (1/4)*L+L
  have hJ : 0≤J := by dsimp [J]; positivity
  have hKJ : Real.exp (1/4)*L+L≤J := by dsimp [J]; linarith
  let ar (t : ℝ) (x : V) : ℝ := Real.exp (-unitClamp t)/16*Af (Real.exp (unitClamp t/4) • x)
  let br (t : ℝ) (x : V) : ℝ := 1/2+Bf (Real.exp (unitClamp t/4) • x)
  have han (t : ℝ) (x : V) : ‖ar t x‖≤M := by
    dsimp [ar]
    rw [abs_mul]
    exact (mul_le_mul (timeweight_bounds (unitClamp_mem t)).2 (hMA _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hab (t : ℝ) (x : V) : ar t x ∈ Icc α M := by
    refine ⟨?_,(le_abs_self _).trans (han t x)⟩
    dsimp [α,ar]
    have he : Real.exp (-1)/16≤Real.exp (-unitClamp t)/16 := by
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [(unitClamp_mem t).2])) (by norm_num)
    exact mul_le_mul he (hκA _) hκ.le (by positivity)
  have hbn (t : ℝ) (x : V) : ‖br t x‖≤M+1 := by
    dsimp [br]
    calc
      _≤‖(1/2:ℝ)‖+‖Bf (Real.exp (unitClamp t/4) • x)‖ := norm_add_le _ _
      _≤M+1 := by have := hMB (Real.exp (unitClamp t/4) • x); norm_num at *; linarith
  have haLip (t r : ℝ) (x z : V) : ‖ar t x-ar r z‖≤J*(‖x-z‖+|unitClamp t-unitClamp r|) :=
    moving_product_joint_lip Af h.2.2.1 M L hM hL hMA (fun y => (hLj y).1)
      (fun y => (hLj y).2.2.1) _ _ (unitClamp_mem t) (unitClamp_mem r) x z
  have hbLip (t r : ℝ) (x z : V) : ‖br t x-br r z‖≤J*(‖x-z‖+|unitClamp t-unitClamp r|) := by
    dsimp [br]
    rw [add_sub_add_left_eq_sub]
    exact (moving_scalar_joint_lip Bf h.2.2.2.1 L hL (fun y => (hLj y).2.1)
      (fun y => (hLj y).2.2.2) _ _ (unitClamp_mem t).2 x z).trans
        (mul_le_mul_of_nonneg_right hKJ (by positivity))
  let a0 (t : ℝ) : V →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (ar t)
    (continuous_const.mul (h.2.2.1.continuous.comp (continuous_const.smul continuous_id))) M (han t)
  let a1 (t : ℝ) : V →ᵇ Icc α M := (a0 t).codRestrict (Icc α M) (hab t)
  let b0 (t : ℝ) : V →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (br t x : ℂ))
    (Complex.continuous_ofReal.comp (continuous_const.add (h.2.2.2.1.continuous.comp (continuous_const.smul continuous_id))))
    (M+1) (fun x => by simpa only [Complex.norm_real] using hbn t x)
  have hcl (t r : ℝ) : |unitClamp t-unitClamp r|≤|t-r| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using unitClamp_lipschitz.dist_le_mul t r
  have hac : LipschitzWith ⟨J,hJ⟩ a1 := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    apply (BoundedContinuousFunction.dist_le (mul_nonneg hJ (dist_nonneg))).mpr
    intro x
    change dist (ar t x) (ar r x)≤J*dist t r
    rw [dist_eq_norm,Real.dist_eq]
    have hj := haLip t r x x
    simp only [sub_self,norm_zero,zero_add] at hj
    exact hj.trans (mul_le_mul_of_nonneg_left (hcl t r) hJ)
  have hbc : LipschitzWith ⟨J,hJ⟩ b0 := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    apply (BoundedContinuousFunction.dist_le (mul_nonneg hJ (dist_nonneg))).mpr
    intro x
    change dist (br t x : ℂ) (br r x : ℂ)≤J*dist t r
    rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.dist_eq]
    have hj := hbLip t r x x
    simp only [sub_self,norm_zero,zero_add] at hj
    exact hj.trans (mul_le_mul_of_nonneg_left (hcl t r) hJ)
  let A : C(ℝ,V →ᵇ Icc α M) := ⟨a1,hac.continuous⟩
  let b : C(ℝ,V →ᵇ ℂ) := ⟨b0,hbc.continuous⟩
  have hAe (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : V) :
      (A t x).val=Real.exp (-t)/16*Af (Real.exp (t/4) • x) := by
    change ar t x=_
    simp only [ar,unitClamp_eq ht]
  have hbe (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : V) :
      b t x=1/2+(Bf (Real.exp (t/4) • x) : ℂ) := by
    change ((br t x : ℝ) : ℂ)=_
    simp only [br,unitClamp_eq ht,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  refine ⟨α,M,C,J,M+1,by dsimp [α]; positivity,hC,hJ,by positivity,A,b,hAe,hbe,?_,?_,?_,?_,?_⟩
  · intro t ht
    exact (BoundedContinuousFunction.norm_le (by positivity : 0≤M+1)).mpr
      (fun x => by change ‖(br t x : ℂ)‖≤_; simpa only [Complex.norm_real] using hbn t x)
  · intro t ht r hr x z
    change |ar t x-ar r z|≤_
    simpa only [Real.norm_eq_abs,unitClamp_eq ht,unitClamp_eq hr] using haLip t r x z
  · intro t ht x z
    change ‖(br t x : ℂ)-(br t z : ℂ)‖≤_
    rw [←Complex.ofReal_sub,Complex.norm_real]
    simpa only [sub_self,abs_zero,add_zero] using hbLip t t x z
  · intro t ht
    simp_rw [hAe t ht]
    exact contDiff_const.mul (h.2.2.1.comp (contDiff_const.smul contDiff_id))
  · intro t ht n hn x
    simp_rw [hAe t ht]
    exact hCj t ht n hn x
end FlatSimilarity

end

end OAI
