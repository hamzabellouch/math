import OAI.Analysis.DiamondDistortion.ModelMaps

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace EquivalentNorm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  seminorm : Seminorm ℝ E
  lowerConstant : ℝ
  upperConstant : ℝ
  lower : ∀ v,‖v‖ ≤ lowerConstant*seminorm v
  upper : ∀ v,seminorm v ≤ upperConstant*‖v‖
namespace Data
variable (A : Data E)
lemma separates (v : E) (hv : A.seminorm v=0) : v=0 := by
  have hh := A.lower v
  rw [hv,mul_zero] at hh
  exact norm_le_zero_iff.mp hh

def Space (_A : Data E) := E
instance : AddCommGroup A.Space := inferInstanceAs (AddCommGroup E)
instance : Module ℝ A.Space := inferInstanceAs (Module ℝ E)
instance : NormedAddCommGroup A.Space := AddGroupNorm.toNormedAddCommGroup
  { A.seminorm.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := A.separates }
instance : NormedSpace ℝ A.Space where
  norm_smul_le t v := le_of_eq (A.seminorm.smul' t v)

def of (v : E) : A.Space := v
def val (v : A.Space) : E := v
@[simp] lemma norm_of (v : E) : ‖A.of v‖=A.seminorm v := rfl

def algebraEquiv : A.Space ≃ₗ[ℝ] E := { LinearEquiv.refl ℝ E with }
def equiv : A.Space ≃L[ℝ] E :=
  A.algebraEquiv.toContinuousLinearEquivOfBounds A.lowerConstant A.upperConstant A.lower A.upper
lemma equiv_apply (v : A.Space) : A.equiv v=A.val v := rfl
lemma equiv_symm_apply (v : E) : A.equiv.symm v=A.of v := rfl
def uniformEquiv : A.Space ≃ᵤ E where
  toEquiv := A.equiv.toEquiv
  uniformContinuous_toFun := A.equiv.toContinuousLinearMap.uniformContinuous
  uniformContinuous_invFun := A.equiv.symm.toContinuousLinearMap.uniformContinuous
instance [CompleteSpace E] : CompleteSpace A.Space :=
  A.uniformEquiv.completeSpace_iff.mpr inferInstance
end Data
end EquivalentNorm

namespace PathModel
open RecursiveModel
lemma quadratic_l2 (h : ℕ) (v : L2 h) :
    ‖v‖ ≤ (Real.sqrt 2*(h+1:ℝ))*cost 2 h v := by
  apply (presentation 2 h).bound v (by positivity : (0:ℝ) ≤ Real.sqrt 2*(h+1:ℝ))
  intro d hd
  change d.fst+path h d.snd=v at hd
  rw [← hd]
  have hb := (norm_add_le d.fst (path h d.snd)).trans (add_le_add le_rfl (path_norm h d.snd))
  have hhn : 1 ≤ (h+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hab : ‖d.fst‖+‖d.snd‖ ≤ Real.sqrt 2*‖d‖ := by
    rw [WithLp.prod_norm_eq_of_L2]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (‖d.fst‖-‖d.snd‖)]
  have hc : ‖d.fst‖+(h+1:ℝ)*‖d.snd‖ ≤ (h+1:ℝ)*(‖d.fst‖+‖d.snd‖) := by
    nlinarith [norm_nonneg d.fst]
  exact (hb.trans hc).trans ((mul_le_mul_of_nonneg_left hab (by positivity)).trans_eq (by ring))

/-- The original underlying ℓ² space endowed with its literal infimal path cost. -/
def linearFullData (h : ℕ) : EquivalentNorm.Data (L2 h) where
  seminorm := cost 1 h
  lowerConstant := h+1
  upperConstant := 1
  lower := linear_l2 h
  upper v := by simpa only [one_mul] using linear_le_norm h v
def quadraticFullData (h : ℕ) : EquivalentNorm.Data (L2 h) where
  seminorm := cost 2 h
  lowerConstant := Real.sqrt 2*(h+1)
  upperConstant := 1
  lower := quadratic_l2 h
  upper v := by simpa only [one_mul] using quadratic_le_norm h v

abbrev LinearComponent (h : ℕ) := (linearFullData h).Space
abbrev QuadraticComponent (h : ℕ) := (quadraticFullData h).Space
abbrev FullLinearSpace := lp (fun h : ℕ => LinearComponent (h+1)) 2
abbrev FullQuadraticSpace := lp (fun h : ℕ => QuadraticComponent (h+1)) 2
end PathModel

namespace CoordinateCompletion.Data
variable {ι E : Type*} (A : CoordinateCompletion.Data ι)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def finiteIsometry (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) : A.Finite →ₗᵢ[ℝ] E where
  toLinearMap := j
  norm_map' := hj

def completionMap (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) : A.Space →L[ℝ] E :=
  (A.finiteIsometry j hj).toContinuousLinearMap.extend UniformSpace.Completion.toComplL
lemma completionMap_coe (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) (v : A.Finite) :
    A.completionMap j hj v=j (A.array v) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) v
lemma completionMap_norm (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) (x : A.Space) :
    ‖A.completionMap j hj x‖=‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (A.completionMap j hj).continuous.norm continuous_norm
  | ih v => rw [A.completionMap_coe,UniformSpace.Completion.norm_coe]; exact hj (A.array v)

def completionIsometry (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) : A.Space →ₗᵢ[ℝ] E where
  toLinearMap := (A.completionMap j hj).toLinearMap
  norm_map' := A.completionMap_norm j hj
lemma completionMap_surjective (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v)
    (hdense : DenseRange j) : Function.Surjective (A.completionIsometry j hj) := by
  have hclosed := (A.completionIsometry j hj).isometry.isClosedEmbedding.isClosed_range
  have hsubset : Set.range j ⊆ Set.range (A.completionIsometry j hj) := by
    rintro _ ⟨v,rfl⟩
    refine ⟨A.embedding v,?_⟩
    exact A.completionMap_coe j hj (A.finite v)
  have hwhole : Set.univ ⊆ Set.range (A.completionIsometry j hj) := by
    rw [← hdense.closure_range]
    exact closure_minimal hsubset hclosed
  exact fun y => hwhole (Set.mem_univ y)
def completionEquiv (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v)
    (hdense : DenseRange j) : A.Space ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective (A.completionIsometry j hj) (A.completionMap_surjective j hj hdense)
end CoordinateCompletion.Data

namespace RecursiveModel
variable {E : ℕ → Type*} [∀ h,NormedAddCommGroup (E h)] [∀ h,NormedSpace ℝ (E h)]
/-- The actual outer Hilbert sum of the component embeddings. -/
def outerEmbedding (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) : ForestVec →ₗ[ℝ] lp E 2 where
  toFun v := ⟨fun h => j h (components v h),(memℓp_zero (by
    apply (v.support.image Sigma.fst).finite_toSet.subset
    intro h hh
    change j h (components v h) ≠ 0 at hh
    by_contra hn
    rw [components_zero v h hn,map_zero] at hh
    exact hh rfl)).of_exponent_ge bot_le⟩
  map_add' v w := by ext h; simp only [map_add,DFinsupp.add_apply,lp.coeFn_add,Pi.add_apply]
  map_smul' c v := by ext h; simp only [map_smul,DFinsupp.smul_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply]
lemma outerEmbedding_apply (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (v : ForestVec) (h : ℕ) :
    outerEmbedding j v h=j h (components v h) := rfl
lemma outerEmbedding_norm (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h)
    (s : ∀ h,Seminorm ℝ (Vec (h+1))) (hj : ∀ h v,‖j h v‖=s h v) (v : ForestVec) :
    ‖outerEmbedding j v‖=outerSeminorm s v := by
  change ‖outerEmbedding j v‖=‖finiteLp 2 (outerValues s v)‖
  have he (h : ℕ) : ‖outerEmbedding j v h‖=‖finiteLp 2 (outerValues s v) h‖ := by
    rw [outerEmbedding_apply,hj,finiteLp_apply,outerValues_apply,Real.norm_eq_abs,abs_of_nonneg (apply_nonneg _ _)]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun h => (he h).le))
    (lp.norm_mono (by norm_num) (fun h => (he h).ge))
lemma outerEmbedding_single (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (h : ℕ) (v : Vec (h+1)) :
    outerEmbedding j (components.symm (DFinsupp.single h v))=lp.single 2 h (j h v) := by
  ext i
  rw [outerEmbedding_apply,LinearEquiv.apply_symm_apply]
  by_cases he : h=i
  · subst i
    rw [DFinsupp.single_eq_same,lp.single_apply_self]
  · rw [DFinsupp.single_eq_of_ne (Ne.symm he),map_zero,lp.single_apply_ne _ _ _ (Ne.symm he)]
lemma outerEmbedding_dense (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (hdense : ∀ h,DenseRange (j h)) :
    DenseRange (outerEmbedding j) := by
  let K := (LinearMap.range (outerEmbedding j)).topologicalClosure
  have hK : IsClosed (K : Set (lp E 2)) := (LinearMap.range (outerEmbedding j)).isClosed_topologicalClosure
  have hfinite (h : ℕ) (v : Vec (h+1)) : lp.single 2 h (j h v) ∈ K := by
    apply subset_closure
    exact ⟨components.symm (DFinsupp.single h v),outerEmbedding_single j h v⟩
  have hsingle (h : ℕ) (x : E h) : lp.single 2 h x ∈ K := by
    induction x using (hdense h).induction_on with
    | hp => exact hK.preimage (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := E) (p := 2) h).continuous
    | ih v => exact hfinite h v
  intro x
  change x ∈ K
  apply hK.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun S => K.sum_mem (fun h _ => hsingle h (x h)))
end RecursiveModel

namespace FiniteLpDensity
variable {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)]
open RecursiveModel
def embedding : (ι →₀ ℝ) →ₗ[ℝ] lp (fun _ : ι => ℝ) p where
  toFun := finiteLp p
  map_add' := finiteLp_add p
  map_smul' := finiteLp_smul p
lemma dense (hp : p ≠ ⊤) : DenseRange (embedding (ι := ι) p) := by
  let K := (LinearMap.range (embedding (ι := ι) p)).topologicalClosure
  have hK : IsClosed (K : Set (lp (fun _ : ι => ℝ) p)) := (LinearMap.range (embedding (ι := ι) p)).isClosed_topologicalClosure
  have hs (i : ι) (c : ℝ) : lp.single p i c ∈ K := by
    apply subset_closure
    refine ⟨Finsupp.single i c,?_⟩
    ext k
    simp only [embedding,LinearMap.coe_mk,AddHom.coe_mk,finiteLp_apply,Finsupp.single_apply,lp.single_apply,Pi.single_apply,eq_comm]
  intro x
  change x ∈ K
  apply hK.mem_of_tendsto (lp.hasSum_single hp x)
  exact Filter.Eventually.of_forall (fun S => K.sum_mem (fun i _ => hs i (x i)))
end FiniteLpDensity

namespace EquivalentNorm.Data
open RecursiveModel
variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : EquivalentNorm.Data (lp (fun _ : ι => ℝ) p))
def coordinateEmbedding : (ι →₀ ℝ) →ₗ[ℝ] A.Space :=
  A.algebraEquiv.symm.toLinearMap.comp (FiniteLpDensity.embedding p)
lemma coordinateEmbedding_norm (v : ι →₀ ℝ) :
    ‖A.coordinateEmbedding v‖=A.seminorm (finiteLp p v) := rfl
lemma coordinateEmbedding_dense (hp : p ≠ ⊤) : DenseRange A.coordinateEmbedding := by
  intro x
  have hh (z : lp (fun _ : ι => ℝ) p) : A.equiv.symm z ∈ closure (range A.coordinateEmbedding) := by
    induction z using (FiniteLpDensity.dense (ι := ι) p hp).induction_on with
    | hp => exact isClosed_closure.preimage A.equiv.symm.continuous
    | ih v => exact subset_closure ⟨v,rfl⟩
  exact hh (A.val x)
end EquivalentNorm.Data

namespace PathModel
open RecursiveModel
def linearFullEmbedding : ForestVec →ₗ[ℝ] FullLinearSpace :=
  outerEmbedding (fun h => (linearFullData (h+1)).coordinateEmbedding)
def quadraticFullEmbedding : ForestVec →ₗ[ℝ] FullQuadraticSpace :=
  outerEmbedding (fun h => (quadraticFullData (h+1)).coordinateEmbedding)
lemma linearFullEmbedding_norm (v : ForestVec) : ‖linearFullEmbedding v‖=linearForestSeminorm v :=
  outerEmbedding_norm _ _ (fun h v => (linearFullData (h+1)).coordinateEmbedding_norm v) v
lemma quadraticFullEmbedding_norm (v : ForestVec) : ‖quadraticFullEmbedding v‖=quadraticForestSeminorm v :=
  outerEmbedding_norm _ _ (fun h v => (quadraticFullData (h+1)).coordinateEmbedding_norm v) v
lemma linearFullEmbedding_dense : DenseRange linearFullEmbedding :=
  outerEmbedding_dense _ (fun h => (linearFullData (h+1)).coordinateEmbedding_dense (by norm_num))
lemma quadraticFullEmbedding_dense : DenseRange quadraticFullEmbedding :=
  outerEmbedding_dense _ (fun h => (quadraticFullData (h+1)).coordinateEmbedding_dense (by norm_num))

def linearFullEquiv : linearData.Space ≃ₗᵢ[ℝ] FullLinearSpace :=
  linearData.completionEquiv linearFullEmbedding linearFullEmbedding_norm linearFullEmbedding_dense
def quadraticFullEquiv : quadraticData.Space ≃ₗᵢ[ℝ] FullQuadraticSpace :=
  quadraticData.completionEquiv quadraticFullEmbedding quadraticFullEmbedding_norm quadraticFullEmbedding_dense
lemma linearFullEquiv_embedding (v : ForestVec) :
    linearFullEquiv (linearData.embedding v)=linearFullEmbedding v := linearData.completionMap_coe _ _ _
lemma quadraticFullEquiv_embedding (v : ForestVec) :
    quadraticFullEquiv (quadraticData.embedding v)=quadraticFullEmbedding v := quadraticData.completionMap_coe _ _ _
end PathModel

namespace LpBoundedMap
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
def normVector (v : lp (fun _ : ι => E) p) : lp (fun _ : ι => ℝ) p :=
  ⟨fun i => ‖v i‖,v.property.norm⟩
lemma normVector_norm {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (v : lp (fun _ : ι => E) p) : ‖normVector v‖=‖v‖ := by
  have he (i : ι) : ‖normVector v i‖=‖v i‖ := norm_norm _
  exact le_antisymm (lp.norm_mono hp (fun i => (he i).le)) (lp.norm_mono hp (fun i => (he i).ge))
def map (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) : lp (fun _ : ι => F) p :=
  ⟨fun i => f (v i),(C • normVector v).property.mono' (fun i => by
    simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
      normVector,abs_norm] using hf (v i))⟩
lemma map_apply {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) (i : ι) : map f C hC hf v i=f (v i) := rfl
lemma map_norm {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) : ‖map f C hC hf v‖ ≤ C*‖v‖ := by
  calc
    _ ≤ ‖C • normVector v‖ := lp.norm_mono hp (fun i => by
      simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
        normVector,abs_norm,map_apply] using hf (v i))
    _ = C*‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,normVector_norm hp]
end LpBoundedMap

end DiamondDistortion

end

end OAI
