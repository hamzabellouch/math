import Mathlib
import OAI.Geometry.SmoothYau.Geometry.PacketAxisShift
import OAI.Geometry.SmoothYau.Limits.CompactProfileUnitLipschitz
import OAI.Geometry.SmoothYau.SphereMetric.UnitCorrelationSymm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace
section NearFarVectors
variable {I : Type} [Fintype I] [DecidableEq I]

def maskComplex (s : Finset I) (v : I → ℂ) : I → ℂ := fun i => if i ∈ s then v i else 0

omit [DecidableEq I] in
lemma complexValueVector_norm_le_sum (v : I → ℂ) :
    ‖complexValueVector v‖ ≤ ∑ i, ‖v i‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset I))
    (f := fun i => ‖v i‖) (fun _ _ => norm_nonneg _)
  rw [←complexValueVector_norm_sq] at hs
  nlinarith [norm_nonneg (complexValueVector v),Finset.sum_nonneg (s := Finset.univ) (f := fun i => ‖v i‖)
    (fun _ _ => norm_nonneg _)]

omit [DecidableEq I] in
lemma complexValueVector_component_le (v : I → ℂ) (i : I) :
    ‖v i‖ ≤ ‖complexValueVector v‖ := by
  have hs := Finset.single_le_sum (f := fun j => ‖v j‖^2) (s := Finset.univ)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [←complexValueVector_norm_sq] at hs
  nlinarith [norm_nonneg (v i),norm_nonneg (complexValueVector v)]

lemma maskComplex_far_error (s : Finset I) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hfar : ∀ i ∉ s, ‖v i‖ ≤ τ) :
    ‖complexValueVector (maskComplex s v)-complexValueVector v‖ ≤ (Fintype.card I : ℝ)*τ := by
  rw [←complexValueVector_sub]
  apply (complexValueVector_norm_le_sum _).trans
  calc
    _ ≤ ∑ _i : I, τ := Finset.sum_le_sum (fun i _ => by
      by_cases hi : i ∈ s
      · simp [maskComplex,hi,hτ]
      · simpa only [maskComplex,ite_eq_right hi,zero_sub,norm_neg] using hfar i hi)
    _ = _ := by simp

lemma maskComplex_norm_ge (s : Finset I) (v : I → ℂ) {A : ℝ}
    (h : ∃ i ∈ s, A ≤ ‖v i‖) : A ≤ ‖complexValueVector (maskComplex s v)‖ := by
  obtain ⟨i,hi,hA⟩ := h
  exact hA.trans (by simpa only [maskComplex,ite_eq_left hi] using
    complexValueVector_component_le (maskComplex s v) i)

lemma masked_endpoint_vector_error (s : Finset I) (v w : I → ℂ) (α : ℝ) (hα : 0 < α)
    (θ : I → ℝ) {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hnear : ∀ i ∈ s, ‖(α : ℂ)*Complex.exp ((θ i : ℂ)*Complex.I)*v i-w i‖ ≤
      ε*‖(α : ℂ)*Complex.exp ((θ i : ℂ)*Complex.I)*v i‖)
    (hfar : ∀ i ∉ s, ‖w i‖ ≤ τ) :
    let z := maskComplex s v
    let b := fun i => (α : ℂ)*rotatedWaveValues z θ i
    ‖complexValueVector b-complexValueVector w‖ ≤
      ε*‖complexValueVector b‖+(Fintype.card I : ℝ)*τ := by
  dsimp only
  let b := fun i => (α : ℂ)*rotatedWaveValues (maskComplex s v) θ i
  have hh : ‖complexValueVector b-complexValueVector (maskComplex s w)‖ ≤
      ε*‖complexValueVector b‖ := by
    apply complexValueVector_relative_error _ _ hε
    intro i
    by_cases hi : i ∈ s
    · simpa only [b,rotatedWaveValues,maskComplex,ite_eq_left hi,mul_assoc,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hα] using hnear i hi
    · simp [b,rotatedWaveValues,maskComplex,hi]
  have ht := norm_add_le (complexValueVector b-complexValueVector (maskComplex s w))
    (complexValueVector (maskComplex s w)-complexValueVector w)
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (add_le_add hh (maskComplex_far_error s w hτ hfar))

lemma masked_rotated_norm (s : Finset I) (v : I → ℂ) {α : ℝ} (hα : 0 < α)
    (θ : I → ℝ) :
    ‖complexValueVector (fun i => (α : ℂ)*rotatedWaveValues (maskComplex s v) θ i)‖ =
      α*‖complexValueVector (maskComplex s v)‖ := by
  rw [complexValueVector_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hα,
    complexValueVector_rotated_norm]

end NearFarVectors

theorem finite_near_far_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (s : Finset I) (v : I → ℂ) (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ)
      (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (A ε δ τ₀ : ℝ) (τ : Fin 3 → ℝ),
      0 < A → 0 ≤ ε → ε ≤ δ → 0 ≤ τ₀ → (∀ j, 0 ≤ τ j) →
      (∃ i ∈ s, A ≤ ‖v i‖) → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
      (∀ i ∈ s, ∀ j, |θ i j| ≤ 1) → (∀ i ∈ s, κ ≤ ∑ j, (θ i j)^2) →
      (∀ i ∉ s, ‖v i‖ ≤ τ₀) → (Fintype.card I : ℝ)*τ₀ ≤ δ*A →
      (∀ j, (Fintype.card I : ℝ)*τ j ≤ (δ-ε)*α j*A) →
      (∀ j i, i ∈ s →
        ‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i-w j i‖ ≤
          ε*‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i‖) →
      (∀ j i, i ∉ s → ‖w j i‖ ≤ τ j) →
      |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0} := by
  obtain ⟨p,hp,hprob⟩ := common_near_wave_sign_probability hκ hκ1
  refine ⟨p,hp,?_⟩
  intro I _ _ s v w α θ m m' A ε δ τ₀ τ hA hε hεδ hτ₀ hτ hlarge hα hδ1 hδκ hθ heng hfar hbasebudget hendbudget hnear hfar' hm hm'
  let z := maskComplex s v
  have hAz : A ≤ ‖complexValueVector z‖ := maskComplex_norm_ge s v hlarge
  have hz : complexValueVector z ≠ 0 := norm_pos_iff.mp (hA.trans_le hAz)
  obtain ⟨i₀,hi₀,_hlarge⟩ := hlarge
  let θ' := fun i j => if i ∈ s then θ i j else θ i₀ j
  have hθ' (i j) : |θ' i j| ≤ 1 := by
    dsimp [θ']; split_ifs with hi
    · exact hθ i hi j
    · exact hθ i₀ hi₀ j
  have heng' (i) : κ ≤ ∑ j, (θ' i j)^2 := by
    by_cases hi : i ∈ s
    · simpa only [θ',ite_eq_left hi] using heng i hi
    · simpa only [θ',ite_eq_right hi] using heng i₀ hi₀
  have hδ : 0 ≤ δ := hε.trans hεδ
  have hbase : ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖ :=
    (maskComplex_far_error s v hτ₀ hfar).trans (hbasebudget.trans
      (mul_le_mul_of_nonneg_left hAz hδ))
  have hend (j) :
      ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ' i j) i)
        -complexValueVector (w j)‖ ≤
      δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ' i j) i)‖ := by
    have hh := masked_endpoint_vector_error s v (w j) (α j) (hα j) (fun i => θ' i j)
      hε (hτ j) (fun i hi => by simpa only [θ',ite_eq_left hi] using hnear j i hi) (hfar' j)
    dsimp only at hh
    change _ ≤ _ at hh
    refine hh.trans ?_
    have hnorm := masked_rotated_norm s v (hα j) (fun i => θ' i j)
    change ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ' i j) i)‖ =
      α j*‖complexValueVector z‖ at hnorm
    rw [hnorm]
    have hb := (hendbudget j).trans (mul_le_mul_of_nonneg_left hAz
      (mul_nonneg (sub_nonneg.mpr hεδ) (hα j).le))
    nlinarith
  exact hprob I z v w α θ' m m' δ hz hα hδ1 hδκ hθ' heng' hbase hend hm hm'
end



section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma finite_packet_variance_lower {I : Type} [Fintype I]
    (φ : NormalWaveSpace → ℝ) {K : Set NormalWaveSpace}
    (q : I → NormalWaveSpace) (U : I → NormalWaveSpace → ℂ)
    (β : I → NormalWaveSpace →L[ℝ] ℝ) {n H M r : ℝ}
    (hn : 1 ≤ n) (hH : 0 ≤ H) (hr : 0 ≤ r) (hnr : n⁻¹ ≤ r) (hMr : M*r ≤ 1/2)
    (hq : ∀ i, q i ∈ K)
    (hφ : ∀ q ∈ K, ∀ x, ‖x-q‖ ≤ 1 → ‖fderiv ℝ φ x‖ ≤ H ∧ |φ x-φ q| ≤ H*‖x-q‖)
    (hu : ∀ i, U i (q i) = Complex.exp ((n : ℂ)*(φ (q i) : ℂ)))
    (hend : ∀ i x, ‖x-q i‖ ≤ r → n*‖x-q i‖ ≤ 1 →
      ‖U i x-(Real.exp (n*fderiv ℝ φ (q i) (x-q i)) : ℂ)*
        Complex.exp (((n*β i (x-q i) : ℝ) : ℂ)*Complex.I)*U i (q i)‖ ≤
          (M*r)*‖(Real.exp (n*fderiv ℝ φ (q i) (x-q i)) : ℂ)*
        Complex.exp (((n*β i (x-q i) : ℝ) : ℂ)*Complex.I)*U i (q i)‖)
    (x : NormalWaveSpace) (hcov : ∃ i, n*‖x-q i‖ ≤ 1) :
    ∃ i, n*‖x-q i‖ ≤ 1 ∧
      (Real.exp (-2*H)/2)*Real.exp (n*φ x) ≤ ‖U i x‖ := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨i,hi⟩ := hcov
  have hdist : ‖x-q i‖ ≤ n⁻¹ := by
    simpa only [mul_one] using (le_inv_mul_iff₀ hn0).mpr hi
  have hdist1 : ‖x-q i‖ ≤ 1 := hdist.trans ((inv_le_one₀ hn0).mpr hn)
  have hq0 : ‖q i-q i‖ ≤ 1 := by simp
  have hφx := hφ (q i) (hq i) x hdist1
  have hφq := hφ (q i) (hq i) (q i) hq0
  exact ⟨i,hi,packet_value_lower_of_endpoint φ hn hH hr hMr hi hφq.1 hφx.2
    (U i) (β i) (hu i) (hend i x (hdist.trans hnr) hi)⟩

lemma finite_packet_standardized_mean {I : Type} [Fintype I]
    (v : I → ℂ) {A m : ℝ} (hA : 0 < A) (hv : ∃ i, A ≤ ‖v i‖) (hm : |m| ≤ A) :
    |m/‖complexValueVector v‖| ≤ 1 := by
  classical
  obtain ⟨i,hi⟩ := hv
  have hnorm : A ≤ ‖complexValueVector v‖ := hi.trans (complexValueVector_component_le v i)
  rw [abs_div,abs_of_pos (hA.trans_le hnorm)]
  exact (div_le_one (hA.trans_le hnorm)).mpr (hm.trans hnorm)
end



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

theorem localized_packet_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (φ : NormalWaveSpace → ℝ) (K : Set NormalWaveSpace)
      (q : I → NormalWaveSpace) (β : I → NormalWaveSpace →L[ℝ] ℝ)
      (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ)
      (H Hs ε ℓ t T c M δ : ℝ) (x : NormalWaveSpace),
      0 ≤ H → 0 ≤ Hs → 0 < ε → ε ≤ 1 → 1 ≤ ℓ → 2 ≤ t →
      0 < T → 0 < c → 0 ≤ M → 0 < δ → δ ≤ 1/16 → δ ≤ κ/96 →
      M*(2/t) ≤ δ/2 → (∀ i, q i ∈ K) → x ∈ K →
      (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
      (∀ y ∈ K, ∃ i, t^4*‖y-q i‖ ≤ 1) →
      (∀ q ∈ K, ∀ y, ‖y-q‖ ≤ 1 → ‖fderiv ℝ φ y‖ ≤ H ∧ |φ y-φ q| ≤ H*‖y-q‖) →
      (∀ j, Real.exp (-Hs) ≤ Real.exp ((ε/ℓ)*fderiv ℝ φ x
        (EuclideanSpace.basisFun (Fin 3) ℝ j))) →
      (∀ i, U i (q i) = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i) : ℂ))) →
      (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-q i‖^2)) →
      (∀ i a y, ‖a-q i‖ ≤ 2/t → ‖y-q i‖ ≤ 2/t → t^4*‖y-a‖ ≤ 1 →
        ‖U i y-(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
          Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖ ≤
        (M*(2/t))*‖(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
          Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖) →
      (∀ i, ‖x-q i‖ ≤ t⁻¹ →
        (∀ j, |ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 1) ∧
        κ ≤ ∑ j, (ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j))^2) →
      (Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4) ≤
        (δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2) →
      (∀ y ∈ K, |b y| ≤ (Real.exp (-2*H)/2)*Real.exp (t^4*φ y)) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
          (b (packetAxisShift x (t^4) ε ℓ j)+
            complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0} := by
  obtain ⟨p,hp,hprob⟩ := finite_near_far_sign_probability hκ hκ1
  refine ⟨p,hp,?_⟩
  intro I _ _ φ K q β U b H Hs ε ℓ t T c M δ x hH hHs hε hε1 hℓ ht hT hc hM hδ hδ1 hδκ hMr hq hx hy hcov hφ hαlo hcenter hloc hend hang hbudget hb
  have ht1 : 1 ≤ t := by linarith
  obtain ⟨ht0,hn1,hinv,hsqrt⟩ := quartic_inverse_bounds ht1
  have hn : 0 < t^4 := by positivity
  have hr : 0 ≤ 2/t := by positivity
  have hnr : (t^4)⁻¹ ≤ 2/t := hinv.trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0])
  have hMrhalf : M*(2/t) ≤ 1/2 := by linarith
  let y : Fin 3 → NormalWaveSpace := packetAxisShift x (t^4) ε ℓ
  let α : Fin 3 → ℝ := fun j => Real.exp ((ε/ℓ)*fderiv ℝ φ x (EuclideanSpace.basisFun (Fin 3) ℝ j))
  let θ : I → Fin 3 → ℝ := fun i j => ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j)
  let A := (Real.exp (-2*H)/2)*Real.exp (t^4*φ x)
  let τ := T*Real.exp H*Real.exp (t^4*φ x)*Real.exp (-c*t^2/4)
  let s : Finset I := Finset.univ.filter (fun i => ‖x-q i‖ ≤ t⁻¹)
  have hA : 0 < A := by dsimp [A]; positivity
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hstep (j) : t^4*‖y j-x‖ ≤ 1 := packetAxisShift_step hn hε.le hε1 hℓ x j
  have hlow (a) (ha : a ∈ K) : ∃ i, t^4*‖a-q i‖ ≤ 1 ∧
      (Real.exp (-2*H)/2)*Real.exp (t^4*φ a) ≤ ‖U i a‖ := by
    apply finite_packet_variance_lower φ q U β hn1 hH hr hnr hMrhalf hq hφ hcenter
      (fun i a ha hstep => hend i (q i) a (by simpa using hr) ha hstep) a (hcov a ha)
  obtain ⟨i₀,hi₀,hlo₀⟩ := hlow x hx
  have hi₀dist : ‖x-q i₀‖ ≤ t⁻¹ := by
    have hh : ‖x-q i₀‖ ≤ (t^4)⁻¹ := by
      simpa only [mul_one] using (le_inv_mul_iff₀ hn).mpr hi₀
    exact hh.trans hinv
  have hlarge : ∃ i ∈ s, A ≤ ‖U i x‖ := ⟨i₀,by simp [s,hi₀dist],hlo₀⟩
  have hnear (j i) (hi : i ∈ s) :
      ‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*U i x-U i (y j)‖ ≤
        (M*(2/t))*‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*U i x‖ := by
    have hix : ‖x-q i‖ ≤ t⁻¹ := (Finset.mem_filter.mp hi).2
    obtain ⟨hxq,hyq⟩ := quartic_near_endpoint ht1 x (y j) (q i) hix (hstep j)
    have hh := hend i x (y j) hxq hyq (hstep j)
    rw [packetAxisShift_covector hn.ne' (by linarith : ℓ ≠ 0) x j (fderiv ℝ φ x),
      packetAxisShift_covector hn.ne' (by linarith : ℓ ≠ 0) x j (β i)] at hh
    change ‖U i (y j)-(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*U i x‖ ≤ _ at hh
    rw [norm_sub_rev]
    exact hh
  have hfar_at (a : NormalWaveSpace) (ha : t^4*‖a-x‖ ≤ 1)
      (hφa : Real.exp (t^4*φ a) ≤ Real.exp H*Real.exp (t^4*φ x))
      (i : I) (hi : i ∉ s) : ‖U i a‖ ≤ τ := by
    have hix : t⁻¹ < ‖x-q i‖ := lt_of_not_ge (by simpa [s] using hi)
    have hd := quartic_far_endpoint ht x a (q i) hix ha
    have hexp : Real.exp (-c*t^4*‖a-q i‖^2) ≤ Real.exp (-c*t^2/4) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hd hc.le]
    apply (hloc i a).trans
    dsimp [τ]
    calc
      _ ≤ T*(Real.exp H*Real.exp (t^4*φ x))*Real.exp (-c*t^2/4) := by gcongr
      _ = _ := by ring
  have hfar₀ (i) (hi : i ∉ s) : ‖U i x‖ ≤ τ := by
    apply hfar_at x (by simp) ?_ i hi
    exact le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp_iff.mpr hH)
  have hfar₁ (j i) (hi : i ∉ s) : ‖U i (y j)‖ ≤ τ := by
    have hd : ‖y j-x‖ ≤ 1 := by nlinarith [hstep j,norm_nonneg (y j-x)]
    exact hfar_at (y j) (hstep j) (profile_exp_close φ hn.le hH x (y j) (hstep j)
      (hφ x hx (y j) hd).2) i hi
  have hα (j) : 0 < α j := Real.exp_pos _
  have htail : (Fintype.card I : ℝ)*τ ≤ (δ/2)*Real.exp (-Hs)*A := by
    have hh := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos (t^4*φ x)).le
    dsimp [τ,A]
    calc
      _ = ((Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4))*Real.exp (t^4*φ x) := by ring
      _ ≤ ((δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2))*Real.exp (t^4*φ x) := hh
      _ = _ := by ring
  have ha01 : Real.exp (-Hs) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hbasebudget : (Fintype.card I : ℝ)*τ ≤ δ*A := by
    apply htail.trans
    have hh := mul_le_mul_of_nonneg_left ha01 (mul_nonneg (half_pos hδ).le hA.le)
    nlinarith
  have hendbudget (j) : (Fintype.card I : ℝ)*τ ≤ (δ-M*(2/t))*α j*A := by
    apply htail.trans
    have hal : Real.exp (-Hs) ≤ α j := hαlo j
    have hh' : (δ/2)*Real.exp (-Hs) ≤ (δ-M*(2/t))*α j := by
      have hn' : δ/2 ≤ δ-M*(2/t) := by linarith
      exact mul_le_mul hn' hal (Real.exp_pos (-Hs)).le (by linarith)
    exact mul_le_mul_of_nonneg_right hh' hA.le
  have hstd : |b x/‖complexValueVector (fun i => U i x)‖| ≤ 1 :=
    finite_packet_standardized_mean _ hA ⟨i₀,hlo₀⟩ (hb x hx)
  have hstd' (j) : |b (y j)/‖complexValueVector (fun i => U i (y j))‖| ≤ 1 := by
    obtain ⟨i,_hi,hlo⟩ := hlow (y j) (hy j)
    exact finite_packet_standardized_mean _ (by positivity) ⟨i,hlo⟩ (hb (y j) (hy j))
  exact hprob I s (fun i => U i x) (fun j i => U i (y j)) α θ (b x) (fun j => b (y j))
    A (M*(2/t)) δ τ (fun _ => τ) hA (mul_nonneg hM hr) (by linarith) hτ (fun _ => hτ)
    hlarge hα hδ1 hδκ
    (fun i hi => (hang i (Finset.mem_filter.mp hi).2).1)
    (fun i hi => (hang i (Finset.mem_filter.mp hi).2).2)
    hfar₀ hbasebudget hendbudget hnear hfar₁ hstd hstd'

end YauCounterexamples
end

end OAI
