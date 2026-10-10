import OAI.Geometry.QuadricBundles.RegularMatrices

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix BinaryForms LaurentCech
open scoped BigOperators
noncomputable section

def powerCoordinates (m : ℕ) (z : BaseCoordinates) : BaseCoordinates := (z.1^m,z.2^m)
lemma powerCoordinates_change (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    powerCoordinates m (coordinateChange i j z)=coordinateChange i j (powerCoordinates m z) := by
  ext <;> simp only [powerCoordinates,coordinateChange,scalarCoordinateChange] <;>
    split_ifs <;> simp [inv_pow]
lemma powerCoordinates_overlap (m : ℕ) {i j : StandardChart} {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) : powerCoordinates m z∈coordinateOverlap i j := by
  rw [coordinateOverlap_iff] at hz ⊢
  exact ⟨hz.1.imp_right (fun h ↦ pow_ne_zero _ h),hz.2.imp_right (fun h ↦ pow_ne_zero _ h)⟩
lemma UniformlyRegularOn.comp_power {U V : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn V f) (m : ℕ) (hm : ∀ z∈U,powerCoordinates m z∈V) :
    UniformlyRegularOn U (fun z ↦ f (powerCoordinates m z)) := by
  apply hf.comp _ _ hm
  · simpa [powerCoordinates,baseEval] using (uniformlyRegular_polynomial U (X 0)).pow m
  · simpa [powerCoordinates,baseEval] using (uniformlyRegular_polynomial U (X 1)).pow m
lemma firstFactor_power (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    firstFactor i j (powerCoordinates m z)=firstFactor i j z^m := by
  simp only [firstFactor,powerCoordinates,scalarFactor]; split_ifs <;> simp
lemma secondFactor_power (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    secondFactor i j (powerCoordinates m z)=secondFactor i j z^m := by
  simp only [secondFactor,powerCoordinates,scalarFactor]; split_ifs <;> simp

namespace EqualizerData
variable (D : EqualizerData)
def flagFrame (m : ℕ) (i : StandardChart) (z : BaseCoordinates) : FlagFrame where
  h := baseEval (D.lift i) (powerCoordinates m z)
  d := baseEval (D.divisor i) (powerCoordinates m z)
  u := baseEval (D.bezoutU i) (powerCoordinates m z)
  v := baseEval (D.bezoutV i) (powerCoordinates m z)
  bezout := D.bezout_eval i _
def flagChange (m : ℕ) (i j : StandardChart) (z : BaseCoordinates) (hz : z∈coordinateOverlap i j) :
    FlagChange (D.flagFrame m i z) (D.flagFrame m j (coordinateChange i j z)) where
  T := D.coordinateTransition i j (powerCoordinates m z)
  kernel := kernelFactor i j (powerCoordinates m z)
  bottom := bottomFactor i j (powerCoordinates m z)
  top := topFactor i j (powerCoordinates m z)
  quotient := quotientFactor i j (powerCoordinates m z)
  kernel_change := by simpa only [flagFrame,powerCoordinates_change] using D.substitute_kernel i j (powerCoordinates_overlap m hz)
  bottom_change := D.substitute_f i j _
  top_projection := D.substitute_e_projection i j _
  lift_quotient := by simpa only [flagFrame,powerCoordinates_change] using D.substitute_lift_quotient i j (powerCoordinates_overlap m hz)

def flagBasis (m t : ℕ) (i : StandardChart) (z : BaseCoordinates) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  (D.flagFrame m i z).matrix t
lemma flagBasis_det_unit (m t : ℕ) (i : StandardChart) (z : BaseCoordinates) :
    IsUnit (D.flagBasis m t i z).det := (D.flagFrame m i z).det_unit t
lemma flagBasis_regular (m t : ℕ) (i : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn univ (fun z ↦ D.flagBasis m t i z a b) := by
  apply adaptedMatrix_regular
  all_goals exact (uniformlyRegular_polynomial univ _).comp_power m (fun _ _ ↦ mem_univ _)

def flagMatrix (m e t : ℕ) (i j : StandardChart) (z : BaseCoordinates) : Matrix (Fin (2*t+1)) (Fin (2*t+1)) ℂ :=
  lineFactor (e,e) i j z • ((D.flagBasis m t i z)⁻¹*
    symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))*
    D.flagBasis m t j (coordinateChange i j z))
lemma flagMatrix_change (m e t : ℕ) (i j : StandardChart) {z : BaseCoordinates} (hz : z∈coordinateOverlap i j) :
    D.flagMatrix m e t i j z=lineFactor (e,e) i j z • (D.flagChange m i j z hz).matrix t := rfl
lemma flagMatrix_regular (m e t : ℕ) (i j : StandardChart) (a b : Fin (2*t+1)) :
    UniformlyRegularOn (coordinateOverlap i j) (fun z ↦ D.flagMatrix m e t i j z a b) := by
  apply (lineFactor_regular (e,e) i j _).mul
  apply UniformlyRegularOn.matrix_mul _ _ a b
  · apply UniformlyRegularOn.matrix_mul
    · exact UniformlyRegularOn.matrix_inv (fun a b ↦ (D.flagBasis_regular m t i a b).mono (subset_univ _))
        (fun z _ ↦ D.flagBasis_det_unit m t i z)
    · exact symmetricMatrix_regular (fun a b ↦ (D.coordinateTransition_regular i j a b).comp_power m
        (fun _ hz ↦ powerCoordinates_overlap m hz)) (2*t)
  · intro a b
    exact (D.flagBasis_regular m t j a b).comp (coordinateChange_fst_regular i j)
      (coordinateChange_snd_regular i j) (fun _ _ ↦ mem_univ _)
lemma flagMatrix_self (m e t : ℕ) (i : StandardChart) (z : BaseCoordinates) :
    D.flagMatrix m e t i i z=1 := by
  simp only [flagMatrix,lineFactor_self,coordinateChange_self,D.coordinateTransition_self,
    symmetricMatrix_one,Matrix.mul_one,one_smul]
  exact Matrix.nonsing_inv_mul _ (D.flagBasis_det_unit m t i z)
lemma flagMatrix_cocycle (m e t : ℕ) (i j k : StandardChart) {z : BaseCoordinates}
    (hj : z∈coordinateOverlap i j) (hk : z∈coordinateOverlap i k) :
    D.flagMatrix m e t i j z*D.flagMatrix m e t j k (coordinateChange i j z)=D.flagMatrix m e t i k z := by
  simp only [flagMatrix,smul_mul,Matrix.mul_smul,smul_smul,
    coordinateChange_comp i j k hj]
  rw [mul_comm (lineFactor (e,e) j k (coordinateChange i j z)),lineFactor_mul_one_overlap (e,e) i j k hj]
  congr 1
  rw [Matrix.mul_assoc,Matrix.mul_assoc,← Matrix.mul_assoc (D.flagBasis m t j (coordinateChange i j z)),
    ← Matrix.mul_assoc (D.flagBasis m t j (coordinateChange i j z)),
    Matrix.mul_nonsing_inv _ (D.flagBasis_det_unit m t j _),Matrix.one_mul,
    ← Matrix.mul_assoc (symmetricMatrix (2*t) (D.coordinateTransition i j (powerCoordinates m z))),
    ← symmetricMatrix_mul,powerCoordinates_change,
    D.coordinateTransition_mul i j k (powerCoordinates_overlap m hj) (powerCoordinates_overlap m hk),
    ← Matrix.mul_assoc]
lemma flagMatrix_triangular (m e t : ℕ) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (a b : Fin (2*t+1)) (hab : b<a) :
    D.flagMatrix m e t i j z a b=0 := by
  rw [D.flagMatrix_change m e t i j hz,Matrix.smul_apply,
    (D.flagChange m i j z hz).triangular_diagonal t |>.1 a b hab,smul_zero]
end EqualizerData
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix BinaryForms LaurentCech EqualizerData
open scoped BigOperators
noncomputable section

def flagDegree (m : ℕ) : (e t : ℕ) → Fin (2*t+1) → ℕ × ℕ
  | e,0 => fun _ ↦ (e,e)
  | e,t+1 => Fin.snoc (n:=2*t+2) (Fin.snoc (n:=2*t+1)
      (flagDegree m (e+18*m) t) (e-3*m+24*m*(2*t+2),e-3*m)) (e,e+24*m*(2*t+2))

lemma power_mul_inv_power (x : ℂ) (hx : x≠0) (a b : ℕ) (hb : b≤a) :
    x^a*(x⁻¹)^b=x^(a-b) := by
  calc
    _ = x^(a-b)*x^b*(x⁻¹)^b := by rw [← pow_add,Nat.sub_add_cancel hb]
    _ = x^(a-b) := by rw [mul_assoc,← mul_pow,mul_inv_cancel₀ hx,one_pow,mul_one]
lemma flag_pen_scalar (m e t : ℕ) (he : 3*m≤e) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor (e,e) i j z*(EqualizerData.kernelFactor i j (powerCoordinates m z)*
      topFactor i j (powerCoordinates m z)^(2*t+1))=
    lineFactor (e-3*m+24*m*(2*t+2),e-3*m) i j z := by
  simp only [lineFactor,EqualizerData.kernelFactor,topFactor,firstFactor_power,secondFactor_power,
    ← inv_pow,← pow_mul]
  have hexp : e+(m*21+(m*24)*(2*t+1))=e-3*m+24*m*(2*t+2) := by
    have hh := Nat.sub_add_cancel he
    nlinarith
  have hs := power_mul_inv_power (secondFactor i j z) (secondFactor_ne_zero hz) e (m*3) (by omega)
  calc
    _ = firstFactor i j z^(e+(m*21+(m*24)*(2*t+1)))*
        (secondFactor i j z^e*(secondFactor i j z)⁻¹^(m*3)) := by
      simp only [pow_add]; ring
    _ = _ := by rw [hexp,hs,show m*3=3*m by omega]
lemma flag_residual_scalar (m e : ℕ) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    lineFactor (e,e) i j z*(EqualizerData.kernelFactor i j (powerCoordinates m z)*
      bottomFactor i j (powerCoordinates m z))=lineFactor (e+18*m,e+18*m) i j z := by
  rw [EqualizerData.kernelFactor_bottomFactor i j (powerCoordinates_overlap m hz)]
  simp only [firstFactor_power,secondFactor_power,lineFactor,mul_pow,← pow_mul,pow_add]
  rw [show m*18=18*m by omega]
  ring
lemma flag_last_scalar (m e t : ℕ) (i j : StandardChart) (z : BaseCoordinates) :
    lineFactor (e,e) i j z*quotientFactor i j (powerCoordinates m z)^(2*(t+1))=
    lineFactor (e,e+24*m*(2*t+2)) i j z := by
  simp only [lineFactor,quotientFactor,secondFactor_power,← pow_mul,pow_add]
  rw [show m*24*(2*(t+1))=24*m*(2*t+2) by ring]
  ring
namespace EqualizerData
variable (D : EqualizerData)
lemma flagChange_graded (m e t : ℕ) (he : 3*m≤e) (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) (a : Fin (2*t+1)) :
    lineFactor (e,e) i j z*(D.flagChange m i j z hz).graded t a=
      lineFactor (flagDegree m e t a) i j z := by
  induction t generalizing e with
  | zero => simp only [FlagChange.graded,flagDegree,mul_one]
  | succ t ih =>
    refine Fin.lastCases (n:=2*t+2) ?_ (fun a ↦ ?_) a
    · simpa only [FlagChange.graded,flagDegree,Fin.snoc_last,flagChange] using flag_last_scalar m e t i j z
    · refine Fin.lastCases (n:=2*t+1) ?_ (fun a ↦ ?_) a
      · simpa only [FlagChange.graded,flagDegree,Fin.snoc_castSucc,Fin.snoc_last,flagChange] using
          flag_pen_scalar m e t he i j hz
      · simp only [FlagChange.graded,flagDegree,Fin.snoc_castSucc]
        rw [← mul_assoc (lineFactor (e,e) i j z)]
        rw [show (D.flagChange m i j z hz).kernel*(D.flagChange m i j z hz).bottom=
          kernelFactor i j (powerCoordinates m z)*bottomFactor i j (powerCoordinates m z) from rfl,
          flag_residual_scalar m e i j hz,ih (e+18*m) (by omega)]

def symmetricFlag (m e t : ℕ) (he : 3*m≤e) : TriangularCechBundle (2*t+1) where
  degree := flagDegree m e t
  matrix := D.flagMatrix m e t
  regular := D.flagMatrix_regular m e t
  self := D.flagMatrix_self m e t
  cocycle := fun i j k z hj hk ↦ D.flagMatrix_cocycle m e t i j k hj hk
  triangular := fun i j z hz a b hab ↦ D.flagMatrix_triangular m e t i j hz a b hab
  diagonal := by
    intro i j z hz a
    rw [D.flagMatrix_change m e t i j hz,Matrix.smul_apply,smul_eq_mul,
      (D.flagChange m i j z hz).triangular_diagonal t |>.2 a]
    exact D.flagChange_graded m e t he i j hz a
end EqualizerData
end
end QuadricCounterexample

end

end OAI
