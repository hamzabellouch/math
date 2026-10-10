import OAI.NumberTheory.DirichletL.PrimeRows.CentralIntegral

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def centralRowIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

lemma scaleBound_eq_rpow_of_one_le {q lo hi : ℝ} (hq : 1≤q) (hl : lo≤hi) :
    scaleBound q lo hi=q^hi := by
  unfold scaleBound
  rw [max_eq_right (mul_le_mul_of_nonneg_left hl (Real.log_nonneg hq)),
    Real.rpow_def_of_pos (by linarith)]

theorem original_row_central_error {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin⟩ := buffered_horizontal_join_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl
  obtain ⟨Ct,hCt,htail⟩ := original_x_height_tail S hS hmax (hfirst.mono_parameter (by linarith)) P hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hZ0 : 0<Z := by linarith
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1)/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    convert hb using 1 ; dsimp [J,k,A] ; ring
  have ht : ‖tail‖≤Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    convert hb using 1 ; dsimp [tail,k,E,A,height] ; rw [abs_of_nonneg hH0] ; ring
  have hdec := (rowIntegral_central_decomposition e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
