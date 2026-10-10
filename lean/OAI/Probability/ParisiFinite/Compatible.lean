import Mathlib
import OAI.Probability.ParisiFinite.SpinWInv

namespace OAI

/-! Compatible. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
namespace PointedTree
open CoherentFock RootSpin
namespace EvenUnitary

 
def Compatible {n : ℕ} (U : EvenUnitary n) (V : EvenUnitary (n+1)) : Prop :=
  ∀x, (empty n).toLinearIsometry (U.op x)=V.op ((empty n).toLinearIsometry x)

theorem Compatible.symm_apply {n : ℕ} {U : EvenUnitary n} {V : EvenUnitary (n+1)}
    (h : Compatible U V) (x : Level n) :
    (empty n).toLinearIsometry (U.op.symm x)=V.op.symm ((empty n).toLinearIsometry x) := by
  apply V.op.injective
  rw [V.op.apply_symm_apply,← h,U.op.apply_symm_apply]

theorem Compatible.insertion {n : ℕ} {U : EvenUnitary n} {V : EvenUnitary (n+1)}
    (h : Compatible U V) : centeredMap (empty n) U.insertion=V.insertion := by
  apply Subtype.ext
  change (empty n).toLinearIsometry (U.op.symm (root n Z (U.op (vac n))))=
    V.op.symm (root (n+1) Z (V.op (vac (n+1))))
  have hv : (empty n).toLinearIsometry (vac n)=vac (n+1) := (empty n).map_vac
  rw [h.symm_apply,root_empty,h,hv]

theorem Compatible.followedBy {n : ℕ} {U₀ V₀ : EvenUnitary n}
    {U₁ V₁ : EvenUnitary (n+1)} (hU : Compatible U₀ U₁) (hV : Compatible V₀ V₁) :
    Compatible (U₀.followedBy V₀) (U₁.followedBy V₁) := by
  intro x
  change (empty n).toLinearIsometry (V₀.op (U₀.op x))=
    V₁.op (U₁.op ((empty n).toLinearIsometry x))
  rw [hV,hU]

theorem compatible_ident (n : ℕ) : Compatible (ident n) (ident (n+1)) := fun _ => rfl

theorem compatible_mixer (n : ℕ) (t : ℝ) : Compatible (mixer n t) (mixer (n+1) t) := by
  intro x
  cases n <;> exact spinMap_root _ _ _

theorem compatible_cost (n : ℕ) (d : Mode n) (e : Mode (n+1))
    (hd : (symmetry n).centered d=-d) (he : (symmetry (n+1)).centered e=-e)
    (h : centeredMap (empty n) d=e) : Compatible (cost n d hd) (cost (n+1) e he) := by
  intro x
  change (empty (n+1)).toLinearIsometry (WZ d x)=WZ e ((empty (n+1)).toLinearIsometry x)
  rw [cost_empty,h]

end EvenUnitary

 

inductive Gate
  | mixer (beta : ℝ)
  | cost (gamma : ℝ)

 
def ordinary : List Gate → (n : ℕ) → EvenUnitary n
  | [], n => EvenUnitary.ident n
  | Gate.mixer beta :: w, n => (ordinary w n).followedBy (EvenUnitary.mixer n beta)
  | Gate.cost gamma :: w, 0 => ordinary w 0
  | Gate.cost gamma :: w, n+1 =>
      (ordinary w (n+1)).followedBy
        (EvenUnitary.cost n ((-(gamma:ℂ)) • (ordinary w n).insertion) (by
          rw [map_smul,EvenUnitary.insertion_odd,smul_neg]))

 
theorem ordinary_compatible (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    EvenUnitary.Compatible (ordinary w n) (ordinary w (n+1)) := by
  induction w generalizing n with
  | nil => exact EvenUnitary.compatible_ident n
  | cons g w ih =>
    cases g with
    | mixer beta =>
      exact (ih n (by simpa using le_trans (Nat.le_succ w.length) hn)).followedBy
        (EvenUnitary.compatible_mixer n beta)
    | cost gamma =>
      cases n with
      | zero => simp at hn
      | succ n =>
        have hn' : w.length ≤ n := by simpa using hn
        apply (ih (n+1) (hn'.trans (Nat.le_succ n))).followedBy
        apply EvenUnitary.compatible_cost
        rw [map_smul,(ih n hn').insertion]

 
theorem ordinary_insertion_empty (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    centeredMap (empty n) (ordinary w n).insertion=(ordinary w (n+1)).insertion :=
  (ordinary_compatible w n hn).insertion

end PointedTree

namespace CoherentFock
open Complex
variable {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]

@[simp] theorem Gamma_expVector (T : E →ₗᵢ[ℂ] F) (d : E) :
    Gamma T (expVector d)=expVector (T d) := by simp [expVector]

@[simp] theorem Gamma_oneParticle (T : E →ₗᵢ[ℂ] F) (d : E) :
    Gamma T (oneParticle d)=oneParticle (T d) := by
  rw [oneParticle,map_smul,map_circleIntegral (Gamma T) (circleIntegrable_oneParticle_integrand d)]
  simp only [map_smul,Gamma_expVector]
  rfl

 

def creationVacuum (d : E) : Space E := (-I) • oneParticle d

def creationEmbedding : E →ₗᵢ[ℂ] Space E where
  toFun := creationVacuum
  map_add' x y := by simp [creationVacuum,oneParticle_add,smul_add]
  map_smul' z x := by
    change (-I) • oneParticleEmbedding (z • x)=z • ((-I) • oneParticleEmbedding x)
    rw [map_smul,smul_comm]
  norm_map' d := by simp [creationVacuum,norm_smul]

@[simp] theorem norm_creationVacuum (d : E) : ‖creationVacuum d‖=‖d‖ := creationEmbedding.norm_map _

@[simp] theorem creationVacuum_orthogonal (d : E) :
    ⟪coherent 0,creationVacuum d⟫_ℂ=0 := by simp [creationVacuum]

@[simp] theorem Gamma_creationVacuum (T : E →ₗᵢ[ℂ] F) (d : E) :
    Gamma T (creationVacuum d)=creationVacuum (T d) := by simp [creationVacuum]
end CoherentFock

namespace PointedTree
open CoherentFock
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

 
def plusEmbedding : H →ₗᵢ[ℂ] SpinOperators.Double H where
  toFun x := WithLp.toLp 2 (fun _ => (((Real.sqrt 2)⁻¹:ℝ):ℂ) • x)
  map_add' x y := by ext i; simp [smul_add]
  map_smul' z x := by ext i; simp [smul_comm z]
  norm_map' x := by
    change ‖WithLp.toLp 2 (fun _ : Fin 2 => (((Real.sqrt 2)⁻¹:ℝ):ℂ) • x)‖=‖x‖
    have hs : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
    have he : ‖WithLp.toLp 2 (fun _ : Fin 2 => (((Real.sqrt 2)⁻¹:ℝ):ℂ) • x)‖^2=‖x‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      change (∑ _:Fin 2, ‖(((Real.sqrt 2)⁻¹:ℝ):ℂ) • x‖^2)=_
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg 2),mul_pow,inv_pow,hs,Fin.sum_univ_two]
      ring
    nlinarith [norm_nonneg x,norm_nonneg (WithLp.toLp 2 (fun _:Fin 2 => (((Real.sqrt 2)⁻¹:ℝ):ℂ) • x))]

@[simp] theorem plusEmbedding_apply (x : H) (i : Fin 2) :
    plusEmbedding x i = (((Real.sqrt 2)⁻¹:ℝ):ℂ) • x := rfl

@[simp] theorem plusEmbedding_coherent_zero :
    plusEmbedding (coherent (0:H))=vacuum H := rfl

@[simp] theorem spinMap_plusEmbedding (T : H →ₗᵢ[ℂ] K) (x : H) :
    spinMap T (plusEmbedding x)=plusEmbedding (T x) := by ext i; simp

 
def rootShift (n : ℕ) : Mode n →ₗᵢ[ℂ] Mode (n+1) where
  toFun d := ⟨plusEmbedding (creationVacuum d),by
    rw [mem_centered]
    change ⟪plusEmbedding (coherent (0:Mode n)),plusEmbedding (creationVacuum d)⟫_ℂ=0
    exact (plusEmbedding.inner_map_map (coherent (0:Mode n)) (creationVacuum d)).trans
      (creationVacuum_orthogonal d)⟩
  map_add' d e := by
    apply Subtype.ext
    change plusEmbedding (creationEmbedding (d+e))=plusEmbedding (creationEmbedding d)+plusEmbedding (creationEmbedding e)
    simp only [map_add]
  map_smul' z d := by
    apply Subtype.ext
    change plusEmbedding (creationEmbedding (z • d))=z • plusEmbedding (creationEmbedding d)
    simp only [map_smul]
  norm_map' d := by exact (plusEmbedding.norm_map _).trans (norm_creationVacuum d)

@[simp] theorem rootShift_coe (n : ℕ) (d : Mode n) :
    (rootShift n d : Level (n+1))=plusEmbedding (creationVacuum d) := rfl

 
@[simp] theorem rootShift_empty (n : ℕ) (d : Mode n) :
    centeredMap (empty (n+1)) (rootShift n d)=rootShift (n+1) (centeredMap (empty n) d) := by
  apply Subtype.ext
  change spinMap (gammaEmbedding (centeredMap (empty n))) (plusEmbedding (creationVacuum d))=
    plusEmbedding (creationVacuum (centeredMap (empty n) d))
  rw [spinMap_plusEmbedding]
  change plusEmbedding (Gamma (centeredMap (empty n)) (creationVacuum d))=_
  rw [Gamma_creationVacuum]

 

def treeEnergy (n : ℕ) (d : Mode n) : ℝ :=
  (⟪centeredMap (empty n) d,rootShift n d⟫_ℂ).re

@[simp] theorem treeEnergy_empty (n : ℕ) (d : Mode n) :
    treeEnergy (n+1) (centeredMap (empty n) d)=treeEnergy n d := by
  unfold treeEnergy
  rw [← rootShift_empty,(centeredMap (empty (n+1))).inner_map_map]

 
theorem treeEnergy_sub_le (n : ℕ) (d e : Mode n) :
    |treeEnergy n d-treeEnergy n e| ≤ (‖d‖+‖e‖)*‖d-e‖ := by
  have he : ⟪centeredMap (empty n) d,rootShift n d⟫_ℂ-
      ⟪centeredMap (empty n) e,rootShift n e⟫_ℂ=
      ⟪centeredMap (empty n) (d-e),rootShift n d⟫_ℂ+
      ⟪centeredMap (empty n) e,rootShift n (d-e)⟫_ℂ := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  change |(⟪centeredMap (empty n) d,rootShift n d⟫_ℂ).re-
    (⟪centeredMap (empty n) e,rootShift n e⟫_ℂ).re| ≤ _
  rw [← Complex.sub_re,he]
  calc
    _ ≤ ‖⟪centeredMap (empty n) (d-e),rootShift n d⟫_ℂ+
      ⟪centeredMap (empty n) e,rootShift n (d-e)⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖⟪centeredMap (empty n) (d-e),rootShift n d⟫_ℂ‖+
      ‖⟪centeredMap (empty n) e,rootShift n (d-e)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖d-e‖*‖d‖+‖e‖*‖d-e‖ := by
      simpa only [LinearIsometry.norm_map] using add_le_add
        (norm_inner_le_norm (𝕜 := ℂ) (centeredMap (empty n) (d-e)) (rootShift n d))
        (norm_inner_le_norm (𝕜 := ℂ) (centeredMap (empty n) e) (rootShift n (d-e)))
    _ = _ := by ring

end PointedTree

namespace ProbeProduct
variable {ι H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def coreAct (S : ι → X → X) : List ι → X → X
  | [],x => x
  | j::l,x => S j (coreAct S l x)

@[simp] theorem coreAct_nil (S : ι → X → X) (x : X) : coreAct S [] x=x := rfl
@[simp] theorem coreAct_cons (S : ι → X → X) (j : ι) (l : List ι) (x : X) :
    coreAct S (j::l) x=S j (coreAct S l x) := rfl

theorem coreAct_bound (S : ι → X → X) (G : X → ℝ) (l : List ι) (C : ℝ)
    (hC : 0 ≤ C) (hS : ∀ j ∈ l, ∀x, G (S j x) ≤ C*G x) (x : X) :
    G (coreAct S l x) ≤ C^l.length*G x := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hi := ih (fun k hk => hS k (by simp [hk]))
    calc
      _ ≤ C*G (coreAct S l x) := hS j (by simp) _
      _ ≤ C*(C^l.length*G x) := mul_le_mul_of_nonneg_left hi hC
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

 

theorem core_perturbation_bound (T : ι → H →L[ℂ] H) (S : ι → X → X)
    (c : X → H) (G : X → ℝ) (hG : ∀x, 0 ≤ G x) (l : List ι) (C ε : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (hT : ∀ j ∈ l, ∀x, ‖T j x‖ ≤ ‖x‖)
    (hS : ∀ j ∈ l, ∀x, G (S j x) ≤ C*G x)
    (hE : ∀ j ∈ l, ∀x, ‖T j (c x)-c (S j x)‖ ≤ ε*G x) (x : X) :
    ‖act T l (c x)-c (coreAct S l x)‖ ≤ ε*l.length*C^l.length*G x := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hTl : ∀ k ∈ l, ∀z, ‖T k z‖ ≤ ‖z‖ := fun k hk => hT k (by simp [hk])
    have hSl : ∀ k ∈ l, ∀z, G (S k z) ≤ C*G z := fun k hk => hS k (by simp [hk])
    have hEl : ∀ k ∈ l, ∀z, ‖T k (c z)-c (S k z)‖ ≤ ε*G z := fun k hk => hE k (by simp [hk])
    have hi := ih hTl hSl hEl
    have hb := coreAct_bound S G l C (by linarith) hSl x
    have he : act T (j::l) (c x)-c (coreAct S (j::l) x)=
        T j (act T l (c x)-c (coreAct S l x))+
          (T j (c (coreAct S l x))-c (S j (coreAct S l x))) := by
      simp only [act_cons,coreAct_cons,map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖T j (act T l (c x)-c (coreAct S l x))‖+
          ‖T j (c (coreAct S l x))-c (S j (coreAct S l x))‖ := norm_add_le _ _
      _ ≤ ε*l.length*C^l.length*G x+ε*G (coreAct S l x) :=
        add_le_add ((hT j (by simp) _).trans hi) (hE j (by simp) _)
      _ ≤ ε*l.length*C^l.length*G x+ε*(C^l.length*G x) := by gcongr
      _ = ε*(l.length+1)*C^l.length*G x := by ring
      _ ≤ ε*(l.length+1)*C^(l.length+1)*G x := by
        apply mul_le_mul_of_nonneg_right _ (hG x)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (Nat.le_succ _))
          (mul_nonneg hε (by positivity))
      _ = _ := by simp

end ProbeProduct

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

def prePhaseZ (θ : ℝ) (x : PreSpin E) : PreSpin E :=
  fun i => Complex.exp (((if i=0 then θ else -θ : ℝ):ℂ)*Complex.I) • x i

@[simp] theorem spinCoe_prePhaseZ (θ : ℝ) (x : PreSpin E) :
    spinCoe (prePhaseZ θ x)=phaseZ θ (spinCoe x) := by
  ext i
  simp only [spinCoe_apply,prePhaseZ,phaseZ_apply,UniformSpace.Completion.coe_smul]

omit [InnerProductSpace ℂ E] in
@[simp] theorem spinBound_prePhaseZ (θ : ℝ) (x : PreSpin E) :
    spinBound (prePhaseZ θ x)=spinBound x := by
  simp only [spinBound,prePhaseZ,secondTailBound_smul,Complex.norm_exp_ofReal_mul_I,one_mul]

def preProbePhase (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (x : PreSpin E) : PreSpin E :=
  preRoot A.conjTranspose (prePhaseZ θ (preRoot A x))

@[simp] theorem spinCoe_preProbePhase (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (x : PreSpin E) :
    spinCoe (preProbePhase A θ x)=probePhase A θ (spinCoe x) := by
  simp only [preProbePhase,spinCoe_preRoot,spinCoe_prePhaseZ,probePhase_apply]

omit [InnerProductSpace ℂ E] in
theorem spinBound_preProbePhase (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (x : PreSpin E) :
    spinBound (preProbePhase A θ x) ≤ matrixMass A.conjTranspose*matrixMass A*spinBound x := by
  unfold preProbePhase
  calc
    _ ≤ matrixMass A.conjTranspose*spinBound (prePhaseZ θ (preRoot A x)) := spinBound_preRoot _ _
    _ = matrixMass A.conjTranspose*spinBound (preRoot A x) := by rw [spinBound_prePhaseZ]
    _ ≤ matrixMass A.conjTranspose*(matrixMass A*spinBound x) :=
      mul_le_mul_of_nonneg_left (spinBound_preRoot _ _) (matrixMass_nonneg _)
    _ = _ := by ring

theorem norm_probe_sub_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (d : E) (x : PreSpin E) :
    ‖probe A d (spinCoe x)-spinCoe x‖ ≤ (‖d‖^2+‖d‖)*matrixMass A*spinBound x := by
  have ht := norm_add_le (probe A d (spinCoe x)-spinCoe x-Complex.I • probeField A d x)
    (Complex.I • probeField A d x)
  rw [sub_add_cancel] at ht
  have h1 := probe_taylor A hA d x
  have h2 := norm_probeField_le A hA d x
  simp only [norm_smul,Complex.norm_I,one_mul] at ht
  nlinarith

theorem coreAct_preProbePhase {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (θ : ι → ℝ) (x : PreSpin E) :
    spinCoe (ProbeProduct.coreAct (fun j => preProbePhase (A j) (θ j)) l x)=
      ProbeProduct.act (fun j => probePhase (A j) (θ j)) l (spinCoe x) := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [ProbeProduct.coreAct_cons,ProbeProduct.act_cons,spinCoe_preProbePhase,ih]

 

theorem centered_product_rotation_bound {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E) (L M : ℝ)
    (hL : 0 ≤ L) (hM : 1 ≤ M) (hA : ∀ j ∈ l, A j ∈ unitary _)
    (hD : ∀ j ∈ l, ‖D j‖ ≤ L)
    (hMass : ∀ j ∈ l, matrixMass (A j) ≤ M)
    (hMassStar : ∀ j ∈ l, matrixMass (A j).conjTranspose ≤ M) (x : PreSpin E) :
    ‖spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e (spinCoe x)))-
        ProbeProduct.act (fun j => probePhase (A j) (-2*(⟪D j,e⟫_ℂ).im)) l (spinCoe x)‖ ≤
      ((L^2+L)*M)*l.length*(M^2)^l.length*spinBound x := by
  rw [← center_probe_product,← coreAct_preProbePhase]
  apply ProbeProduct.core_perturbation_bound _ _ spinCoe spinBound spinBound_nonneg l (M^2) ((L^2+L)*M)
  · nlinarith
  · positivity
  · intro j hj z
    simp only [ContinuousLinearMap.comp_apply,norm_spinW,norm_probe _ (hA j hj)]
    rfl
  · intro j hj z
    calc
      _ ≤ matrixMass (A j).conjTranspose*matrixMass (A j)*spinBound z := spinBound_preProbePhase _ _ _
      _ ≤ M*M*spinBound z := by
        gcongr
        · exact spinBound_nonneg _
        · exact matrixMass_nonneg _
        · exact hMassStar j hj
        · exact hMass j hj
      _ = _ := by ring
  · intro j hj z
    simp only [ContinuousLinearMap.comp_apply,spinCoe_preProbePhase]
    rw [centered_toggled_probe _ (hA j hj),← map_sub,norm_probePhase _ (hA j hj)]
    calc
      _ ≤ (‖D j‖^2+‖D j‖)*matrixMass (A j)*spinBound z := norm_probe_sub_le _ (hA j hj) _ _
      _ ≤ ((L^2+L)*M)*spinBound z := by
        gcongr
        · exact spinBound_nonneg _
        · exact matrixMass_nonneg _
        · exact hD j hj
        · exact hD j hj
        · exact hMass j hj

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem phaseZ_add (θ φ : ℝ) (x : SpinSpace E) :
    phaseZ θ (phaseZ φ x)=phaseZ (θ+φ) x := by
  ext i
  simp only [phaseZ_apply,smul_smul]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  split_ifs <;> push_cast <;> ring

theorem phaseZ_sub_phaseZ_le (θ φ : ℝ) (x : SpinSpace E) :
    ‖phaseZ θ x-phaseZ φ x‖ ≤ |θ-φ| *‖x‖ := by
  have he : phaseZ θ x-phaseZ φ x=phaseZ φ (phaseZ (θ-φ) x-x) := by
    rw [map_sub,phaseZ_add,show φ+(θ-φ)=θ by ring]
  rw [he,norm_phaseZ]
  exact phaseZ_sub_le _ _

theorem probePhase_sub_probePhase_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (θ φ : ℝ) (x : SpinSpace E) :
    ‖probePhase A θ x-probePhase A φ x‖ ≤ |θ-φ| *‖x‖ := by
  simp only [probePhase_apply,← map_sub,SpinOperators.norm_act (root_adjoint_unitary A hA)]
  simpa only [SpinOperators.norm_act hA] using phaseZ_sub_phaseZ_le θ φ (SpinOperators.act A x)

 

theorem rotation_product_bound {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (θ φ : ι → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hA : ∀ j ∈ l, A j ∈ unitary _)
    (hp : ∀ j ∈ l, |θ j-φ j| ≤ α) (x : SpinSpace E) :
    ‖ProbeProduct.act (fun j => probePhase (A j) (θ j)) l x-
      ProbeProduct.act (fun j => probePhase (A j) (φ j)) l x‖ ≤ l.length*α*‖x‖ := by
  apply ProbeProduct.perturbation_bound _ _ l α hα
  · intro j hj z
    exact (norm_probePhase _ (hA j hj) _ z).le
  · intro j hj z
    exact (norm_probePhase _ (hA j hj) _ z).le
  · intro j hj z
    exact (probePhase_sub_probePhase_le _ (hA j hj) _ _ z).trans
      (mul_le_mul_of_nonneg_right (hp j hj) (norm_nonneg z))

 

theorem special_product_bound {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E) (φ : ι → ℝ)
    (L M α : ℝ) (hL : 0 ≤ L) (hM : 1 ≤ M) (hα : 0 ≤ α)
    (hA : ∀ j ∈ l, A j ∈ unitary _) (hD : ∀ j ∈ l, ‖D j‖ ≤ L)
    (hMass : ∀ j ∈ l, matrixMass (A j) ≤ M)
    (hMassStar : ∀ j ∈ l, matrixMass (A j).conjTranspose ≤ M)
    (hp : ∀ j ∈ l, |(-2*(⟪D j,e⟫_ℂ).im)-φ j| ≤ α) (x : PreSpin E) :
    ‖spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e (spinCoe x)))-
      ProbeProduct.act (fun j => probePhase (A j) (φ j)) l (spinCoe x)‖ ≤
      ((L^2+L)*M)*l.length*(M^2)^l.length*spinBound x+l.length*α*‖spinCoe x‖ := by
  have h1 := centered_product_rotation_bound l A D e L M hL hM hA hD hMass hMassStar x
  have h2 := rotation_product_bound l A (fun j => -2*(⟪D j,e⟫_ℂ).im) φ α hα hA hp (spinCoe x)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e (spinCoe x))))
    (ProbeProduct.act (fun j => probePhase (A j) (-2*(⟪D j,e⟫_ℂ).im)) l (spinCoe x))
    (ProbeProduct.act (fun j => probePhase (A j) (φ j)) l (spinCoe x))
  linarith

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem scaled_translated_spin_bound (d e : E) (x y : PreSpin E) (B δ R : ℝ)
    (hx : SpinRadiusLE x B) (hy : SpinRadiusLE y B) (hδ : 0 < δ)
    (hsep : δ ≤ ‖d-e‖) (hR : 1 ≤ R) (hB : 4*B ≤ R*δ) :
    ‖⟪spinW (R • d) (spinCoe x),spinW (R • e) (spinCoe y)⟫_ℂ‖ ≤
      spinMass x*spinMass y*Real.exp (-(δ^2/8)*R) := by
  rw [PiLp.inner_apply]
  calc
    _ ≤ ∑ i : Fin 2, ‖⟪W (R • d) (↑(x i)),W (R • e) (↑(y i))⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, mass (x i)*mass (y i)*Real.exp (-(δ^2/8)*R) := by
      exact Finset.sum_le_sum (fun i _ => scaled_translated_pre_bound d e (x i) (y i) B δ R
        (hx i) (hy i) hδ hsep hR hB)
    _ ≤ ∑ i : Fin 2, mass (x i)*spinMass y*Real.exp (-(δ^2/8)*R) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact mass_nonneg _
      · exact mass_le_spinMass _ _
    _ = _ := by simp only [spinMass,Finset.sum_mul]

 

theorem scaled_spin_matrix_bound (P : Matrix (Fin 2) (Fin 2) ℂ) (d e : E)
    (x y : PreSpin E) (B δ R : ℝ)
    (hx : SpinRadiusLE x B) (hy : SpinRadiusLE y B) (hδ : 0 < δ)
    (hsep : δ ≤ ‖d-e‖) (hR : 1 ≤ R) (hB : 4*B ≤ R*δ) :
    ‖⟪SpinOperators.act P (spinW (R • d) (spinCoe x)),spinW (R • e) (spinCoe y)⟫_ℂ‖ ≤
      matrixMass P*spinMass x*spinMass y*Real.exp (-(δ^2/8)*R) := by
  rw [← spinW_root,← spinCoe_preRoot]
  apply (scaled_translated_spin_bound d e (preRoot P x) y B δ R
    (hx.preRoot P) hy hδ hsep hR hB).trans
  gcongr
  · exact spinMass_nonneg _
  · exact spinMass_preRoot _ _

 

theorem rapid_decay_spin_matrix {α : Type*} {l : Filter α}
    (R : α → ℝ) (d e : α → E) (x y : α → PreSpin E)
    (P : α → Matrix (Fin 2) (Fin 2) ℂ) (hR : Tendsto R l atTop)
    (B A C δ : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hx : ∀ᶠ a in l, SpinRadiusLE (x a) B ∧ spinMass (x a) ≤ A)
    (hy : ∀ᶠ a in l, SpinRadiusLE (y a) B ∧ spinMass (y a) ≤ A)
    (hP : ∀ᶠ a in l, matrixMass (P a) ≤ C)
    (hsep : ∀ᶠ a in l, δ ≤ ‖d a-e a‖) (M : ℕ) :
    Tendsto (fun a => (R a)^M *
      ‖⟪SpinOperators.act (P a) (spinW (R a • d a) (spinCoe (x a))),
        spinW (R a • e a) (spinCoe (y a))⟫_ℂ‖) l (𝓝 0) := by
  have hR1 : ∀ᶠ a in l, 1 ≤ R a := hR.eventually (eventually_ge_atTop 1)
  have hRB : ∀ᶠ a in l, 4*B ≤ R a*δ := by
    filter_upwards [hR.eventually (eventually_ge_atTop (4*B/δ))] with a ha
    exact (div_le_iff₀ hδ).mp ha
  have he : Tendsto (fun t : ℝ => t^M*Real.exp (-(δ^2/8)*t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M:ℝ) (δ^2/8) (by positivity)
  have he' := (he.comp hR).const_mul (C*A*A)
  simp only [mul_zero] at he'
  apply squeeze_zero' _ _ he'
  · filter_upwards [hR1] with a ha
    exact mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)
  · filter_upwards [hR1,hRB,hx,hy,hP,hsep] with a ha hba hxa hya hpa hsa
    have hb := scaled_spin_matrix_bound (P a) (d a) (e a) (x a) (y a) B δ (R a)
      hxa.1 hya.1 hδ hsa ha hba
    calc
      _ ≤ (R a)^M*(matrixMass (P a)*spinMass (x a)*spinMass (y a)*Real.exp (-(δ^2/8)*R a)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)
      _ ≤ (R a)^M*(C*A*A*Real.exp (-(δ^2/8)*R a)) := by
        gcongr
        · exact spinMass_nonneg _
        · exact spinMass_nonneg _
        · exact hxa.2
        · exact hya.2
      _ = _ := by dsimp only [Function.comp_def]; ring

end CoherentFock

open scoped InnerProductSpace ComplexConjugate
namespace PacketGeometry
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]

 
theorem symmetric_diagonal_im (P : H →ₗ[ℂ] H)
    (hP : ∀ x y, ⟪P x,y⟫_ℂ=⟪x,P y⟫_ℂ) (x : H) :
    (⟪P x,x⟫_ℂ).im=0 := by
  have h := congrArg Complex.im (hP x x)
  have hc := congrArg Complex.im (inner_conj_symm x (P x))
  simp only [Complex.conj_im] at hc
  linarith

 

theorem huge_center_imaginary (P : H →ₗ[ℂ] H)
    (hP : ∀ x y, ⟪P x,y⟫_ℂ=⟪x,P y⟫_ℂ)
    (hPN : ∀x, ‖P x‖ ≤ ‖x‖) (xp xm s z : H) :
    |(⟪P (xp+xm+s),xp-xm+z⟫_ℂ).im| ≤
      2*‖⟪P xp,xm⟫_ℂ‖ + ‖⟪P xp,z⟫_ℂ‖ + ‖⟪P xm,z⟫_ℂ‖ +
        ‖⟪P s,xp⟫_ℂ‖ + ‖⟪P s,xm⟫_ℂ‖ + ‖s‖*‖z‖ := by
  have hd1 := symmetric_diagonal_im P hP xp
  have hd2 := symmetric_diagonal_im P hP xm
  have hc : ⟪P xm,xp⟫_ℂ=conj ⟪P xp,xm⟫_ℂ := by
    rw [hP]
    exact (inner_conj_symm _ _).symm
  have he : (⟪P (xp+xm+s),xp-xm+z⟫_ℂ).im =
      (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ+⟪P xm,xp⟫_ℂ+
        ⟪P xm,z⟫_ℂ+⟪P s,xp⟫_ℂ-⟪P s,xm⟫_ℂ+⟪P s,z⟫_ℂ).im := by
    simp only [map_add,inner_add_left,inner_add_right,inner_sub_right,
      Complex.add_im,Complex.sub_im,Complex.neg_im,hd1,hd2]
    ring
  rw [he]
  have h0 := Complex.abs_im_le_norm
    (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ+⟪P xm,xp⟫_ℂ+
      ⟪P xm,z⟫_ℂ+⟪P s,xp⟫_ℂ-⟪P s,xm⟫_ℂ+⟪P s,z⟫_ℂ)
  have h1 := norm_add_le
    (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ+⟪P xm,xp⟫_ℂ+
      ⟪P xm,z⟫_ℂ+⟪P s,xp⟫_ℂ-⟪P s,xm⟫_ℂ) ⟪P s,z⟫_ℂ
  have h2 := norm_sub_le (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ+⟪P xm,xp⟫_ℂ+
      ⟪P xm,z⟫_ℂ+⟪P s,xp⟫_ℂ) ⟪P s,xm⟫_ℂ
  have h3 := norm_add_le (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ+⟪P xm,xp⟫_ℂ+
      ⟪P xm,z⟫_ℂ) ⟪P s,xp⟫_ℂ
  have h4 := norm_add_le (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ+⟪P xm,xp⟫_ℂ) ⟪P xm,z⟫_ℂ
  have h5 := norm_add_le (-⟪P xp,xm⟫_ℂ+⟪P xp,z⟫_ℂ) ⟪P xm,xp⟫_ℂ
  have h6 := norm_add_le (-⟪P xp,xm⟫_ℂ) ⟪P xp,z⟫_ℂ
  have h7 := (norm_inner_le_norm (𝕜 := ℂ) (P s) z).trans (mul_le_mul_of_nonneg_right (hPN s) (norm_nonneg z))
  rw [norm_neg] at h6
  have hcn : ‖⟪P xm,xp⟫_ℂ‖=‖⟪P xp,xm⟫_ℂ‖ := by rw [hc,Complex.norm_conj]
  rw [hcn] at h5
  linarith

 

theorem inner_remainder_bound (P : H →ₗ[ℂ] H) (hPN : ∀x, ‖P x‖ ≤ ‖x‖)
    (x y ρ σ : H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hx : ‖x+ρ‖ ≤ 1) (hy : ‖y+σ‖ ≤ 1) (hρ : ‖ρ‖ ≤ δ) (hσ : ‖σ‖ ≤ δ) :
    ‖⟪P (x+ρ),y+σ⟫_ℂ-⟪P x,y⟫_ℂ‖ ≤ δ*(2+δ) := by
  have hxn : ‖x‖ ≤ 1+δ := by
    have he : x=(x+ρ)-ρ := by abel
    calc
      ‖x‖ = ‖(x+ρ)-ρ‖ := congrArg norm he
      _ ≤ ‖x+ρ‖+‖ρ‖ := norm_sub_le _ _
      _ ≤ 1+δ := add_le_add hx hρ
  have he : ⟪P (x+ρ),y+σ⟫_ℂ-⟪P x,y⟫_ℂ =
      ⟪P ρ,y+σ⟫_ℂ+⟪P x,σ⟫_ℂ := by
    simp only [map_add,inner_add_left,inner_add_right]
    ring
  rw [he]
  calc
    _ ≤ ‖⟪P ρ,y+σ⟫_ℂ‖+‖⟪P x,σ⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖ρ‖*‖y+σ‖+‖x‖*‖σ‖ := by
      exact add_le_add ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans
        (mul_le_mul_of_nonneg_right (hPN _) (norm_nonneg _)))
        ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans
        (mul_le_mul_of_nonneg_right (hPN _) (norm_nonneg _)))
    _ ≤ δ*1+(1+δ)*δ := by gcongr
    _ = _ := by ring

 

theorem huge_imaginary_modulus (P : H →ₗ[ℂ] H)
    (hP : ∀ x y, ⟪P x,y⟫_ℂ=⟪x,P y⟫_ℂ)
    (hPN : ∀x, ‖P x‖ ≤ ‖x‖) (xp xm s z ρ σ : H) (δ ε a : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hx : ‖xp+xm+s+ρ‖ ≤ 1) (hy : ‖xp-xm+z+σ‖ ≤ 1)
    (hρ : ‖ρ‖ ≤ δ) (hσ : ‖σ‖ ≤ δ) (hs : ‖s‖ ≤ a) (hz : ‖z‖ ≤ a)
    (h1 : ‖⟪P xp,xm⟫_ℂ‖ ≤ ε) (h2 : ‖⟪P xp,z⟫_ℂ‖ ≤ ε)
    (h3 : ‖⟪P xm,z⟫_ℂ‖ ≤ ε) (h4 : ‖⟪P s,xp⟫_ℂ‖ ≤ ε)
    (h5 : ‖⟪P s,xm⟫_ℂ‖ ≤ ε) :
    |(⟪P (xp+xm+s+ρ),xp-xm+z+σ⟫_ℂ).im| ≤ 6*ε+a^2+δ*(2+δ) := by
  have hb := huge_center_imaginary P hP hPN xp xm s z
  have hr := inner_remainder_bound P hPN (xp+xm+s) (xp-xm+z) ρ σ δ hδ hx hy hρ hσ
  have hd := Complex.abs_im_le_norm
    (⟪P (xp+xm+s+ρ),xp-xm+z+σ⟫_ℂ-⟪P (xp+xm+s),xp-xm+z⟫_ℂ)
  simp only [Complex.sub_im] at hd
  have ht := abs_add_le
    ((⟪P (xp+xm+s+ρ),xp-xm+z+σ⟫_ℂ).im-(⟪P (xp+xm+s),xp-xm+z⟫_ℂ).im)
    (⟪P (xp+xm+s),xp-xm+z⟫_ℂ).im
  have hsz : ‖s‖*‖z‖ ≤ a*a := mul_le_mul hs hz (norm_nonneg _) ha
  simp only [sub_add_cancel] at ht
  nlinarith

end PacketGeometry

end

end OAI
