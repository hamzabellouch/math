import OAI.Analysis.Naimark.Extension

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

def CARStage : ℕ → Type
  | 0 => ℂ
  | n+1 => CStarMatrix Bool Bool (CARStage n)

@[instance_reducible] private def carStageCStarAux : ∀ n, CStarAlgebra (CARStage n) :=
  Nat.rec (inferInstanceAs (CStarAlgebra ℂ)) (fun n ih => by
    letI : CStarAlgebra (CARStage n) := ih
    letI : PartialOrder (CARStage n) := CStarAlgebra.spectralOrder _
    letI : StarOrderedRing (CARStage n) := CStarAlgebra.spectralOrderedRing _
    exact inferInstanceAs (CStarAlgebra (CStarMatrix Bool Bool (CARStage n))))

instance carStageCStar (n : ℕ) : CStarAlgebra (CARStage n) := carStageCStarAux n

instance carStagePartialOrder (n : ℕ) : PartialOrder (CARStage n) :=
  CStarAlgebra.spectralOrder _
instance carStageStarOrder (n : ℕ) : StarOrderedRing (CARStage n) :=
  CStarAlgebra.spectralOrderedRing _

instance carStageNontrivial : ∀ n, Nontrivial (CARStage n)
  | 0 => inferInstanceAs (Nontrivial ℂ)
  | n+1 => by
    let := carStageNontrivial n
    exact inferInstanceAs (Nontrivial (CStarMatrix Bool Bool (CARStage n)))

instance carStageSimple : ∀ n, IsSimpleRing (CARStage n)
  | 0 => inferInstanceAs (IsSimpleRing ℂ)
  | n+1 => by
    let := carStageSimple n
    change IsSimpleRing (Matrix Bool Bool (CARStage n))
    infer_instance

def matrixScalarHom (A : Type*) [CStarAlgebra A] : A →⋆ₐ[ℂ] CStarMatrix Bool Bool A where
  toFun a := CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => a))
  map_zero' := by change Matrix.diagonal (fun _ : Bool => (0:A)) = 0; simp
  map_one' := by change Matrix.diagonal (fun _ : Bool => (1:A)) = 1; simp
  map_add' a b := by
    change Matrix.diagonal (fun _ : Bool => a+b) =
      Matrix.diagonal (fun _ : Bool => a) + Matrix.diagonal (fun _ : Bool => b)
    exact (Matrix.diagonal_add _ _).symm
  map_mul' a b := by
    change Matrix.diagonal (fun _ : Bool => a*b) = _
    exact (Matrix.diagonal_mul_diagonal _ _).symm
  commutes' z := by
    change Matrix.diagonal (fun _ : Bool => algebraMap ℂ A z) = _
    exact (Matrix.algebraMap_eq_diagonal z).symm
  map_star' a := by
    change Matrix.diagonal (fun _ : Bool => star a) =
      (Matrix.diagonal (fun _ : Bool => a)).conjTranspose
    exact (Matrix.diagonal_conjTranspose _).symm

@[simp] theorem matrixScalarHom_entry (A : Type*) [CStarAlgebra A] (a : A) (i : Bool) :
    (matrixScalarHom A a) i i = a := by simp [matrixScalarHom]

theorem matrixScalarHom_injective (A : Type*) [CStarAlgebra A] :
    Function.Injective (matrixScalarHom A) := by
  intro a b h
  simpa only [matrixScalarHom_entry] using
    congrArg (fun x : CStarMatrix Bool Bool A => x false false) h

theorem matrixScalarHom_isometry (A : Type*) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    Isometry (matrixScalarHom A) :=
  NonUnitalStarAlgHom.isometry _ (matrixScalarHom_injective A)

def carStep (n : ℕ) : CARStage n →⋆ₐ[ℂ] CARStage (n+1) := matrixScalarHom (CARStage n)

def carBond (n m : ℕ) (h : n ≤ m) : CARStage n →⋆ₐ[ℂ] CARStage m :=
  Nat.leRec (StarAlgHom.id ℂ (CARStage n)) (fun {k} _ g => (carStep k).comp g) h

@[simp] theorem carBond_self (n : ℕ) : carBond n n le_rfl = StarAlgHom.id _ _ := by
  simp only [carBond,Nat.leRec_self]

@[simp] theorem carBond_succ (n m : ℕ) (h : n ≤ m) :
    carBond n (m+1) (Nat.le.step h) = (carStep m).comp (carBond n m h) := by
  simp only [carBond,Nat.leRec_succ _ _ h]

theorem carBond_comp (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    (carBond m k hmk).comp (carBond n m hnm) = carBond n k (hnm.trans hmk) := by
  induction hmk with
  | refl => simp
  | @step k hmk ih =>
    rw [carBond_succ m k hmk,carBond_succ n k (hnm.trans hmk),StarAlgHom.comp_assoc,ih]

instance carDirected : DirectedSystem CARStage (fun n m h => carBond n m h) where
  map_self n a := by rw [carBond_self]; rfl
  map_map k m n hnm hmk a := by
    exact congrArg (fun g : CARStage n →⋆ₐ[ℂ] CARStage k => g a) (carBond_comp n m k hnm hmk)

theorem carBond_isometry (n m : ℕ) (h : n ≤ m) : Isometry (carBond n m h) := by
  induction h with
  | refl => rw [carBond_self]; exact isometry_id
  | @step m h ih =>
    rw [carBond_succ n m h]
    exact (matrixScalarHom_isometry (CARStage m)).comp ih

open scoped ComplexOrder CStarAlgebra

instance carIsometricSystem : IsometricStarSystem CARStage carBond := ⟨carBond_isometry⟩

abbrev CAR := CStarDirectLimit CARStage carBond

abbrev carInclude (n : ℕ) : CARStage n →⋆ₐ[ℂ] CAR :=
  cstarDirectLimitInclude CARStage carBond n

theorem carInclude_isometry (n : ℕ) : Isometry (carInclude n) :=
  cstarDirectLimitInclude_isometry CARStage carBond n

instance carNontrivial : Nontrivial CAR := cstarDirectLimit_nontrivial CARStage carBond 0

instance carOrder : PartialOrder CAR := CStarAlgebra.spectralOrder _
instance carStarOrder : StarOrderedRing CAR := CStarAlgebra.spectralOrderedRing _

instance carStageFinite : ∀ n, Module.Finite ℂ (CARStage n)
  | 0 => inferInstanceAs (Module.Finite ℂ ℂ)
  | n+1 => by
    let := carStageFinite n
    change Module.Finite ℂ (Matrix Bool Bool (CARStage n))
    infer_instance

theorem carStage_finrank (n : ℕ) : Module.finrank ℂ (CARStage n) = 4^n := by
  induction n with
  | zero => exact Module.finrank_self ℂ
  | succ n ih =>
    change Module.finrank ℂ (Matrix Bool Bool (CARStage n)) = _
    rw [Module.finrank_matrix,ih]
    simp [pow_succ]
    omega

theorem carSimple : IsSimpleCStar CAR := by
  apply simple_of_dense_stage_ranges CARStage _ carInclude carInclude_isometry
    (cstarDirectLimitInclude_dense CARStage carBond)
  intro n
  refine ⟨inferInstance,fun J _ => ?_⟩
  exact eq_bot_or_eq_top J

instance carSeparable : TopologicalSpace.SeparableSpace CAR := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  rw [← (cstarDirectLimitInclude_dense CARStage carBond).closure_eq]
  apply TopologicalSpace.IsSeparable.closure
  apply TopologicalSpace.IsSeparable.iUnion
  intro n
  exact TopologicalSpace.isSeparable_range (carInclude_isometry n).continuous

theorem carInfiniteDimensional : ¬ Module.Finite ℂ CAR := by
  intro hf
  let := hf
  have hle (n : ℕ) : 4^n ≤ Module.finrank ℂ CAR := by
    rw [← carStage_finrank n]
    exact LinearMap.finrank_le_finrank_of_injective (f := (carInclude n).toLinearMap)
      (carInclude_isometry n).injective
  have hg := hle (Module.finrank ℂ CAR+1)
  have hp := Nat.lt_pow_self (n := Module.finrank ℂ CAR+1) (a := 4) (by norm_num)
  omega

open scoped ComplexOrder CStarAlgebra

theorem complex_identity_isState : IsState (ContinuousLinearMap.id ℂ ℂ) := by
  rw [isState_iff]
  refine ⟨rfl,fun a => ?_⟩
  have h := star_mul_self_nonneg a
  exact ⟨h.2.symm,h.1⟩

def carStageTrace : ∀ n, {τ : CARStage n →L[ℂ] ℂ // IsState τ} :=
  Nat.rec ⟨ContinuousLinearMap.id ℂ ℂ,complex_identity_isState⟩ (fun _ T =>
    ⟨matrixTraceState T.1 T.2,matrixTraceState_isState T.1 T.2⟩)

@[simp] theorem carStageTrace_zero (z : ℂ) : (carStageTrace 0).1 z = z := rfl

@[simp] theorem carStageTrace_succ (n : ℕ) (M : CARStage (n+1)) :
    (carStageTrace (n+1)).1 M = matrixTraceState (carStageTrace n).1 (carStageTrace n).2 M := rfl

theorem carStageTrace_tracial (n : ℕ) (a b : CARStage n) :
    (carStageTrace n).1 (a*b) = (carStageTrace n).1 (b*a) := by
  induction n with
  | zero => exact @mul_comm ℂ inferInstance a b
  | succ n ih => exact matrixTraceState_tracial (carStageTrace n).1 (carStageTrace n).2 ih a b

theorem carStageTrace_step (n : ℕ) (a : CARStage n) :
    (carStageTrace (n+1)).1 (carStep n a) = (carStageTrace n).1 a := by
  change (2:ℝ)⁻¹ • (∑ i : Bool, (carStageTrace n).1 (matrixScalarHom _ a i i)) = _
  simp only [matrixScalarHom_entry,Fintype.sum_bool,← two_smul ℝ]
  rw [smul_smul,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),one_smul]

theorem carStageTrace_compatible (n m : ℕ) (hnm : n ≤ m) (a : CARStage n) :
    (carStageTrace m).1 (carBond n m hnm a) = (carStageTrace n).1 a := by
  induction hnm with
  | refl => rw [carBond_self]; rfl
  | @step m h ih => rw [carBond_succ n m h,StarAlgHom.comp_apply,carStageTrace_step,ih]

def carTrace : CAR →L[ℂ] ℂ := cstarDirectLimitState CARStage carBond
  (fun n => (carStageTrace n).1) (fun n => (carStageTrace n).2) carStageTrace_compatible

theorem carTrace_isState : IsState carTrace := cstarDirectLimitState_isState _ _ _ _ _

@[simp] theorem carTrace_stage (n : ℕ) (a : CARStage n) :
    carTrace (carInclude n a) = (carStageTrace n).1 a := cstarDirectLimitState_stage _ _ _ _ _ n a

theorem carTrace_tracial (a b : CAR) : carTrace (a*b) = carTrace (b*a) :=
  cstarDirectLimitState_tracial _ _ _ _ _ carStageTrace_tracial a b

theorem carTrace_faithful (a : CAR) (ha : a ≠ 0) : 0 < (carTrace (star a*a)).re :=
  tracialState_strictPos_of_simple carSimple carTrace carTrace_isState carTrace_tracial a ha

def carStageVector : ∀ n, {f : CARStage n →L[ℂ] ℂ // IsState f} :=
  Nat.rec ⟨ContinuousLinearMap.id ℂ ℂ,complex_identity_isState⟩ (fun _ f =>
    ⟨matrixState f.1 false,matrixState_isState f.1 f.2 false⟩)

theorem carStageVector_step (n : ℕ) (a : CARStage n) :
    (carStageVector (n+1)).1 (carStep n a) = (carStageVector n).1 a := by
  exact congrArg (carStageVector n).1 (matrixScalarHom_entry _ a false)

theorem carStageVector_compatible (n m : ℕ) (hnm : n ≤ m) (a : CARStage n) :
    (carStageVector m).1 (carBond n m hnm a) = (carStageVector n).1 a := by
  induction hnm with
  | refl => rw [carBond_self]; rfl
  | @step m h ih => rw [carBond_succ n m h,StarAlgHom.comp_apply,carStageVector_step,ih]

def carVector : CAR →L[ℂ] ℂ := cstarDirectLimitState CARStage carBond
  (fun n => (carStageVector n).1) (fun n => (carStageVector n).2) carStageVector_compatible

theorem carVector_isState : IsState carVector := cstarDirectLimitState_isState _ _ _ _ _

@[simp] theorem carVector_stage (n : ℕ) (a : CARStage n) :
    carVector (carInclude n a) = (carStageVector n).1 a := cstarDirectLimitState_stage _ _ _ _ _ n a

open scoped ComplexOrder CStarAlgebra

def carStagePeak : ∀ n, CARStage n
  | 0 => 1
  | n+1 => matrixSingle false false (carStagePeak n)

theorem carStagePeak_projection (n : ℕ) : IsStarProjection (carStagePeak n) := by
  induction n with
  | zero => exact IsStarProjection.one ℂ
  | succ n ih => exact matrixSingle_projection false (carStagePeak n) ih

theorem carStagePeak_compress (n : ℕ) (a : CARStage n) :
    carStagePeak n*a*carStagePeak n = (carStageVector n).1 a • carStagePeak n := by
  induction n with
  | zero =>
    let z : ℂ := a
    change (1:ℂ)*z*1 = z • (1:ℂ)
    simp
  | succ n ih =>
    let M : CStarMatrix Bool Bool (CARStage n) := a
    change matrixSingle false false (carStagePeak n)*M*matrixSingle false false (carStagePeak n) = _
    rw [matrixSingle_compress,ih]
    exact matrixSingle_smul false false (carStagePeak n) ((carStageVector n).1 (M false false))

@[simp] theorem carStageVector_peak (n : ℕ) : (carStageVector n).1 (carStagePeak n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (carStageVector n).1 (matrixSingle false false (carStagePeak n) false false) = 1
    simpa only [matrixSingle_apply, and_self, eq_self_iff_true, ite_true] using ih

@[simp] theorem carStageTrace_peak (n : ℕ) : (carStageTrace n).1 (carStagePeak n) = (2:ℂ)⁻¹^n := by
  induction n with
  | zero => change (1:ℂ) = (2:ℂ)⁻¹^0; simp
  | succ n ih =>
    rw [carStageTrace_succ]
    change matrixTraceState (carStageTrace n).1 (carStageTrace n).2
      (matrixSingle false false (carStagePeak n)) = _
    rw [matrixTraceState_single,ih]
    norm_num [pow_succ,Complex.real_smul]
    ring

theorem carStagePeak_bond (n : ℕ) :
    carStep n (carStagePeak n) * carStagePeak (n+1) = carStagePeak (n+1) := by
  change Matrix.diagonal (fun _ : Bool => carStagePeak n) * Matrix.single false false (carStagePeak n) = _
  ext i j
  rw [Matrix.diagonal_mul]
  change carStagePeak n * (if false = i ∧ false = j then carStagePeak n else 0) =
    (if false = i ∧ false = j then carStagePeak n else 0)
  split_ifs
  · exact (carStagePeak_projection n).isIdempotentElem.eq
  · exact mul_zero _

def carPeak (n : ℕ) : CAR := carInclude n (carStagePeak n)

@[simp] theorem carPeak_zero : carPeak 0 = 1 := map_one _

theorem carPeak_projection (n : ℕ) : IsStarProjection (carPeak n) :=
  (carStagePeak_projection n).map (carInclude n)

theorem carPeak_antitone : Antitone carPeak := by
  apply antitone_nat_of_succ_le
  intro n
  apply ((carPeak_projection (n+1)).le_iff_mul_eq_right (carPeak_projection n)).mpr
  change carInclude n (carStagePeak n) * carInclude (n+1) (carStagePeak (n+1)) = _
  have hb := cstarDirectLimitInclude_compatible CARStage carBond n (n+1) (Nat.le_succ n) (carStagePeak n)
  rw [carBond_succ n n le_rfl, carBond_self, StarAlgHom.comp_apply] at hb
  change carInclude (n+1) (carStep n (carStagePeak n)) = carInclude n (carStagePeak n) at hb
  rw [← hb,← map_mul,carStagePeak_bond]
  rfl

@[simp] theorem carVector_peak (n : ℕ) : carVector (carPeak n) = 1 := by
  rw [carPeak,carVector_stage,carStageVector_peak]

@[simp] theorem carTrace_peak (n : ℕ) : carTrace (carPeak n) = (2:ℂ)⁻¹^n := by
  rw [carPeak,carTrace_stage,carStageTrace_peak]

theorem carPeak_unique (g : CAR →L[ℂ] ℂ) (hg : IsState g)
    (hp : ∀ n, g (carPeak n) = 1) : g = carVector := by
  ext x
  apply cstarDirectLimit_induction CARStage carBond (P := fun x => g x = carVector x)
    (isClosed_eq g.continuous carVector.continuous) _ x
  intro n a
  have he := state_compression g hg (carPeak n) ((carPeak_projection n).norm_le _)
    (carPeak_projection n).isSelfAdjoint (hp n) (carInclude n a)
  rw [carVector_stage]
  rw [← he]
  change g (carInclude n (carStagePeak n) * carInclude n a * carInclude n (carStagePeak n)) = _
  rw [← map_mul,← map_mul,carStagePeak_compress,map_smul,map_smul]
  change (carStageVector n).1 a • g (carPeak n) = _
  rw [hp n,smul_eq_mul,mul_one]

theorem carPeak_peaks : Peaks carPeak carVector :=
  ⟨carPeak_projection,carPeak_antitone,carVector_isState,carVector_peak,carPeak_unique⟩

theorem carVector_isPure : IsPureState carVector := carPeak_peaks.isPureState

open scoped ComplexOrder CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A]

theorem matrixScalar_eq_sum_single (a : A) : matrixScalarHom A a =
    matrixSingle false false a + matrixSingle true true a := by
  ext i j
  cases i <;> cases j <;> simp [matrixScalarHom,matrixSingle_apply,Matrix.diagonal]

theorem trace_two_corners (f : CStarMatrix Bool Bool A →ₗ[ℂ] ℂ)
    (htr : ∀ a b, f (a*b) = f (b*a)) (a : A) :
    f (matrixSingle false false a) = f (matrixSingle true true a) := by
  simpa only [matrixSingle_mul,mul_one,one_mul] using
    htr (matrixSingle false true a) (matrixSingle true false 1)

theorem trace_matrix_corner (f : CStarMatrix Bool Bool A →ₗ[ℂ] ℂ)
    (htr : ∀ a b, f (a*b) = f (b*a)) (a : A) :
    f (matrixScalarHom A a) = 2 * f (matrixSingle false false a) := by
  rw [matrixScalar_eq_sum_single,map_add,← trace_two_corners f htr,two_mul]

end

open scoped ComplexOrder CStarAlgebra
section

theorem carStage_normalizedTrace_peak (n : ℕ) (f : CARStage n →ₗ[ℂ] ℂ)
    (h1 : f 1 = 1) (htr : ∀ a b, f (a*b) = f (b*a)) :
    f (carStagePeak n) = (2:ℂ)⁻¹^n := by
  induction n with
  | zero => simpa only [carStagePeak, pow_zero] using h1
  | succ n ih =>
    let F : CStarMatrix Bool Bool (CARStage n) →ₗ[ℂ] ℂ := f
    have hFtr (a b) : F (a*b) = F (b*a) := htr a b
    let g : CARStage n →ₗ[ℂ] ℂ := f.comp (carStep n).toLinearMap
    have hg1 : g 1 = 1 := by
      change f (carStep n 1) = 1
      rw [map_one,h1]
    have hgtr (a b : CARStage n) : g (a*b) = g (b*a) := by
      change f (carStep n (a*b)) = f (carStep n (b*a))
      rw [map_mul (carStep n),map_mul (carStep n),htr]
    have hi := ih g hg1 hgtr
    have hc := trace_matrix_corner F hFtr (carStagePeak n)
    change F (matrixSingle false false (carStagePeak n)) = _
    change F (matrixScalarHom (CARStage n) (carStagePeak n)) = _ at hi
    calc
      F (matrixSingle false false (carStagePeak n)) =
          (2:ℂ)⁻¹ * F (matrixScalarHom (CARStage n) (carStagePeak n)) := by
        rw [hc]
        ring
      _ = (2:ℂ)⁻¹^(n+1) := by rw [hi,pow_succ]; ring

variable {B : Type*} [CStarAlgebra B]

theorem carPeak_ambientTrace (φ : CAR →⋆ₐ[ℂ] B) (τ : B →ₗ[ℂ] ℂ)
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a*b) = τ (b*a)) (n : ℕ) :
    τ (φ (carPeak n)) = (2:ℂ)⁻¹^n := by
  apply carStage_normalizedTrace_peak n
    (τ.comp (φ.comp (carInclude n)).toLinearMap)
  · change τ ((φ.comp (carInclude n)) 1) = 1
    rw [map_one,h1]
  · intro a b
    change τ ((φ.comp (carInclude n)) (a*b)) = τ ((φ.comp (carInclude n)) (b*a))
    rw [map_mul (φ.comp (carInclude n)),map_mul (φ.comp (carInclude n)),htr]

theorem carPeak_autTrace (φ : CAR →⋆ₐ[ℂ] B) (γ : B ≃⋆ₐ[ℂ] B)
    (τ : B →ₗ[ℂ] ℂ) (h1 : τ 1 = 1) (htr : ∀ a b, τ (a*b) = τ (b*a)) (n : ℕ) :
    τ (γ (φ (carPeak n))) = (2:ℂ)⁻¹^n :=
  carPeak_ambientTrace (γ.toStarAlgHom.comp φ) τ h1 htr n

end

open Filter Topology
open scoped ComplexOrder CStarAlgebra
section

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem Peaks.mapEquiv {p : ℕ → B} {f g : B →L[ℂ] ℂ} (hp : Peaks p f)
    (γ : B ≃⋆ₐ[ℂ] B) (hg : IsState g) (he : restrictState γ.toStarAlgHom g = f) :
    Peaks (fun n => γ (p n)) g := by
  refine ⟨fun n => (hp.1 n).map γ, fun m n h => OrderHomClass.mono γ (hp.2.1 h),
    hg, ?_, ?_⟩
  · intro n
    change restrictState γ.toStarAlgHom g (p n) = 1
    rw [he]
    exact hp.2.2.2.1 n
  · intro G hG hGp
    have hr := hp.2.2.2.2 _ (isState_restrict γ.toStarAlgHom G hG) hGp
    ext a
    obtain ⟨b,rfl⟩ := γ.surjective a
    exact (congrArg (fun h : B →L[ℂ] ℂ => h b) hr).trans
      (congrArg (fun h : B →L[ℂ] ℂ => h b) he).symm

private theorem complexInvTwoPow_re (n : ℕ) :
    ((2:ℂ)⁻¹^n).re = (1/2:ℝ)^n := by
  have hc : (2:ℂ)⁻¹ = ((1/2:ℝ):ℂ) := by norm_num
  rw [hc, ← Complex.ofReal_pow, Complex.ofReal_re]

variable (ψ : CAR →⋆ₐ[ℂ] B) (φ : B →⋆ₐ[ℂ] A) (hφ : Function.Injective φ)
  (f g : A →L[ℂ] ℂ) (hp : Peaks (fun n => φ (ψ (carPeak n))) f)
  (hg : IsPureState (restrictState φ g)) (hgs : IsState g)
  (hu : PureUEP φ) (γ : B ≃⋆ₐ[ℂ] B)
  (he : restrictState γ.toStarAlgHom (restrictState φ g) = restrictState φ f)

include hφ hp hg hgs hu he in

theorem homogeneousCARPeak_peaks : Peaks (fun n => φ (γ (ψ (carPeak n)))) g := by
  have hsmall := (hp.restrict φ hφ).1
  exact (hsmall.mapEquiv γ (isState_restrict φ g hgs) he).extend φ
    (hu _ hg) g hgs rfl

def homogeneousCARPeakPair (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ)
    (hn : τ 1 = 1) (hfaith : ∀ a, τ (star a*a) = 0 → a = 0) :
    PeakingPairData A where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hfaith
  peak i n := if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))
  state i := if i then g else f
  peaks i := by
    cases i
    · exact hp
    · exact homogeneousCARPeak_peaks ψ φ hφ f g hp hg hgs hu γ he
  peak_zero i := by cases i <;> simp only [Bool.false_eq_true, ↓reduceIte, carPeak_zero, map_one]
  atom_positive i n := by
    have htrace (i : Bool) (n : ℕ) :
        τ (if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))) = (2:ℂ)⁻¹^n := by
      cases i
      · exact carPeak_ambientTrace (φ.comp ψ) τ.toLinearMap hn htr n
      · exact carPeak_ambientTrace (φ.comp (γ.toStarAlgHom.comp ψ)) τ.toLinearMap hn htr n
    change 0 < (τ ((if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))) -
      (if i then φ (γ (ψ (carPeak (n+1)))) else φ (ψ (carPeak (n+1)))))).re
    rw [map_sub,htrace,htrace,Complex.sub_re]
    rw [complexInvTwoPow_re,complexInvTwoPow_re,pow_succ]
    have h : (0:ℝ) < (1/2:ℝ)^n := pow_pos (by norm_num) n
    linarith
  trace_null i := by
    have htrace (n : ℕ) :
        τ (if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))) = (2:ℂ)⁻¹^n := by
      cases i
      · exact carPeak_ambientTrace (φ.comp ψ) τ.toLinearMap hn htr n
      · exact carPeak_ambientTrace (φ.comp (γ.toStarAlgHom.comp ψ)) τ.toLinearMap hn htr n
    simp_rw [htrace]
    have hh : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [complexInvTwoPow_re] using hh
  matched i n := by
    cases i
    · rfl
    · change τ (φ (γ (ψ (carPeak n)))) = τ (φ (ψ (carPeak n)))
      exact (carPeak_ambientTrace (φ.comp (γ.toStarAlgHom.comp ψ)) τ.toLinearMap hn htr n).trans
        (carPeak_ambientTrace (φ.comp ψ) τ.toLinearMap hn htr n).symm

end

end NaimarkZFC

end

end OAI
