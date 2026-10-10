import OAI.Probability.ClassicalON.CylindricalGeometry

namespace OAI

noncomputable section
open MeasureTheory
namespace ClassicalON

def firstAmplitude (s : Spin 3) : Amplitude := ⟨|s.val 0|,abs_nonneg _,by
  simpa only [Real.norm_eq_abs,spin_norm] using PiLp.norm_apply_le s.val 0⟩

theorem continuous_firstAmplitude : Continuous firstAmplitude := by
  apply Continuous.subtype_mk
  exact ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val).abs

@[simp] theorem firstAmplitude_cylindricalSpin (r : Amplitude) (τ : Bool) (θ : PlanarAngle) :
    firstAmplitude (cylindricalSpin r τ θ)=r := by
  apply Subtype.ext
  change |(r:ℝ)*signValue τ|=(r:ℝ)
  cases τ <;> simp [signValue,abs_of_nonneg r.property.1]

theorem planarAngle_exists (a b : ℝ) (hab : a^2+b^2=1) :
    ∃ θ : PlanarAngle,planarCos θ=a ∧ planarSin θ=b := by
  let z : Circle := ⟨⟨a,b⟩,by
    change (⟨a,b⟩ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [← Complex.normSq_eq_norm_sq]
    simpa [Complex.normSq_apply,pow_two] using hab⟩
  obtain ⟨θ,hθ⟩ := (AddCircle.homeomorphCircle (T := (1:ℝ)) (by norm_num)).surjective z
  rw [AddCircle.homeomorphCircle_apply] at hθ
  exact ⟨θ,congrArg (fun z : Circle => (z:ℂ).re) hθ,congrArg (fun z : Circle => (z:ℂ).im) hθ⟩

theorem cylindricalSpin_surjective_fiber (s : Spin 3) :
    ∃ τ θ,cylindricalSpin (firstAmplitude s) τ θ=s := by
  let r := firstAmplitude s
  let q := transverseAmplitude r
  have hq : q^2=s.val 1^2+s.val 2^2 := by
    have hh := normSq_three s.val
    rw [spin_norm] at hh
    have hr : (r:ℝ)^2=s.val 0^2 := sq_abs _
    dsimp only [q]
    rw [transverseAmplitude_sq,hr]
    nlinarith
  obtain ⟨τ,hτ⟩ : ∃ τ,(r:ℝ)*signValue τ=s.val 0 := by
    by_cases hs : 0 ≤ s.val 0
    · exact ⟨true,by simp [r,firstAmplitude,signValue,abs_of_nonneg hs]⟩
    · exact ⟨false,by simp [r,firstAmplitude,signValue,abs_of_neg (lt_of_not_ge hs)]⟩
  by_cases hzero : q=0
  · refine ⟨τ,0,Subtype.ext ?_⟩
    ext i
    have h1 : s.val 1=0 := by nlinarith [sq_nonneg (s.val 2)]
    have h2 : s.val 2=0 := by nlinarith [sq_nonneg (s.val 1)]
    fin_cases i
    · exact hτ
    · change q*planarCos 0=s.val 1
      rw [hzero,h1,zero_mul]
    · change q*planarSin 0=s.val 2
      rw [hzero,h2,zero_mul]
  · have hab : (s.val 1/q)^2+(s.val 2/q)^2=1 := by
      field_simp
      nlinarith
    obtain ⟨θ,hc,hs⟩ := planarAngle_exists _ _ hab
    refine ⟨τ,θ,Subtype.ext ?_⟩
    ext i
    fin_cases i
    · exact hτ
    · change q*planarCos θ=s.val 1
      rw [hc,mul_div_cancel₀ _ hzero]
    · change q*planarSin θ=s.val 2
      rw [hs,mul_div_cancel₀ _ hzero]

theorem cylinderRotation_cylindricalSpin (τ υ : Bool) (θ φ : PlanarAngle) (r : Amplitude) :
    spinRotation (cylinderRotation τ θ) (cylindricalSpin r υ φ)=
      cylindricalSpin r (τ==υ) (θ+φ) := by
  apply Subtype.ext
  ext i
  fin_cases i
  · change signValue τ*((r:ℝ)*signValue υ)=(r:ℝ)*signValue (τ==υ)
    cases τ <;> cases υ <;> simp [signValue]
  · change planarCos θ*(transverseAmplitude r*planarCos φ)-
      planarSin θ*(transverseAmplitude r*planarSin φ)=transverseAmplitude r*planarCos (θ+φ)
    rw [planarCos_add]; ring
  · change planarSin θ*(transverseAmplitude r*planarCos φ)+
      planarCos θ*(transverseAmplitude r*planarSin φ)=transverseAmplitude r*planarSin (θ+φ)
    rw [planarSin_add]; ring

theorem continuous_cylinderSpinRotation :
    Continuous (fun p : (Bool×PlanarAngle)×Spin 3 =>
      spinRotation (cylinderRotation p.1.1 p.1.2) p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => cylinderLinear p.1.1 p.1.2 p.2.val)
  unfold cylinderLinear
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hc : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => planarCos p.1.2) := continuous_planarCos.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => planarSin p.1.2) := continuous_planarSin.comp (continuous_snd.comp continuous_fst)
  have ht : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => signValue p.1.1) := (show Continuous signValue from continuous_of_discreteTopology).comp (continuous_fst.comp continuous_fst)
  have hv (j : Fin 3) : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => p.2.val j) := (PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd)
  fin_cases i
  · exact ht.mul (hv 0)
  · exact (hc.mul (hv 1)).sub (hs.mul (hv 2))
  · exact (hs.mul (hv 1)).add (hc.mul (hv 2))

end ClassicalON

end

end OAI
