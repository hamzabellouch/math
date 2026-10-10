import OAI.Analysis.DiamondDistortion.LpDual

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

open scoped Classical
open Filter Topology

namespace RecursiveModel
lemma exponent_real_gt_one (h : ℕ) : 1 < (exponent h).toReal := by
  unfold exponent
  rw [ENNReal.toReal_add ENNReal.one_ne_top (by simp),ENNReal.toReal_one,ENNReal.toReal_inv]
  rw [ENNReal.toReal_add (by simp) ENNReal.one_ne_top]
  simp only [ENNReal.toReal_natCast,ENNReal.toReal_one]
  have hpos : 0 < (h:ℝ)+1 := by positivity
  linarith [inv_pos.mpr hpos]

instance vectorComponentDualSeparable (h : ℕ) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (VectorComponent h)) := by
  let : TopologicalSpace.SeparableSpace (StrongDual ℝ (Full (exponent h) (h+1))) :=
    LpDual.dual_separable (fun _ : Coord (h+1) => ℝ) (exponent h) (exponent_real_gt_one h)
  let e := (fullData (exponent h) (exponent_real_pos h) (h+1)).equiv.symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)
  exact e.surjective.denseRange.separableSpace e.continuous

instance fullVectorDualSeparable : TopologicalSpace.SeparableSpace (StrongDual ℝ FullVectorSpace) :=
  LpDual.dual_separable VectorComponent 2 (by norm_num)
instance vectorDualSeparable : TopologicalSpace.SeparableSpace (StrongDual ℝ VectorSpace) := by
  let e := fullVectorEquiv.symm.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  exact e.surjective.denseRange.separableSpace e.continuous
end RecursiveModel

namespace CoordinateCompletion.Data
variable {ι κ E : Type*} (A : CoordinateCompletion.Data ι)
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma coordinate_of_equiv (e : A.Space ≃ₗᵢ[ℝ] E) (i : ι) (c : E →L[ℝ] ℝ)
    (hj : ∀ v,c (e (A.embedding v))=v i) (x : A.Space) : c (e x)=A.coordinate i x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (c.continuous.comp e.continuous) (A.coordinate i).continuous
  | ih v =>
    rw [A.coordinate_coe]
    change c (e (A.embedding (A.array v))) = _
    exact hj (A.array v)
lemma transported_projection_coordinate (e : A.Space ≃ₗᵢ[ℝ] E) (i : ι) (c : E →L[ℝ] ℝ)
    (hj : ∀ v,c (e (A.embedding v))=v i)
    (H : κ → Finset ι) (hcover : ∀ S : Finset ι,∃ h,S ⊆ H h) (h : κ) (x : E) :
    c (((A.heads H hcover).transport e).projection h x)=if i ∈ H h then c x else 0 := by
  change c (e (A.projection (H h) (e.symm x)))=_
  rw [A.coordinate_of_equiv e i c hj,A.coordinate_projection,
    ← A.coordinate_of_equiv e i c hj,e.apply_symm_apply]
end CoordinateCompletion.Data

namespace EquivalentNorm.Data
variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (A : EquivalentNorm.Data (lp (fun _ : ι => ℝ) p))
def coordinate (i : ι) : A.Space →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : ι => ℝ) p i).comp A.equiv.toContinuousLinearMap
lemma coordinate_apply (i : ι) (x : A.Space) : A.coordinate i x=A.val x i := rfl
lemma coordinate_embedding (i : ι) (v : ι →₀ ℝ) : A.coordinate i (A.coordinateEmbedding v)=v i := rfl
end EquivalentNorm.Data

namespace RecursiveModel
variable {E : ℕ → Type*} [∀ h,NormedAddCommGroup (E h)] [∀ h,NormedSpace ℝ (E h)]
def outerCoordinate (c : ∀ h,Coord (h+1) → E h →L[ℝ] ℝ) (i : ForestCoord) : lp E 2 →L[ℝ] ℝ :=
  (c i.1 i.2).comp (lp.evalCLM ℝ E 2 i.1)
lemma outerCoordinate_apply (c : ∀ h,Coord (h+1) → E h →L[ℝ] ℝ) (i : ForestCoord) (x : lp E 2) :
    outerCoordinate c i x=c i.1 i.2 (x i.1) := rfl
lemma outerCoordinate_embedding (c : ∀ h,Coord (h+1) → E h →L[ℝ] ℝ)
    (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (hc : ∀ h i v,c h i (j h v)=v i) (i : ForestCoord) (v : ForestVec) :
    outerCoordinate c i (outerEmbedding j v)=v i := by
  rw [outerCoordinate_apply,outerEmbedding_apply,hc,components_apply]
end RecursiveModel

namespace PathModel
open RecursiveModel
def linearFullCoordinate : ForestCoord → FullLinearSpace →L[ℝ] ℝ :=
  outerCoordinate (fun h => (linearFullData (h+1)).coordinate)
def quadraticFullCoordinate : ForestCoord → FullQuadraticSpace →L[ℝ] ℝ :=
  outerCoordinate (fun h => (quadraticFullData (h+1)).coordinate)
lemma linearFullCoordinate_equiv (i : ForestCoord) (x : LinearSpace) :
    linearFullCoordinate i (linearFullEquiv x)=linearData.coordinate i x :=
  linearData.coordinate_of_equiv linearFullEquiv i (linearFullCoordinate i) (fun v => by
    rw [linearFullEquiv_embedding]
    rfl) x
lemma quadraticFullCoordinate_equiv (i : ForestCoord) (x : QuadraticSpace) :
    quadraticFullCoordinate i (quadraticFullEquiv x)=quadraticData.coordinate i x :=
  quadraticData.coordinate_of_equiv quadraticFullEquiv i (quadraticFullCoordinate i) (fun v => by
    rw [quadraticFullEquiv_embedding]
    rfl) x

lemma linearFullHeads_coordinate (H : ForestHead) (x : FullLinearSpace) (i : ForestCoord) :
    linearFullCoordinate i (linearFullHeads.projection H x)=if i ∈ H.val then linearFullCoordinate i x else 0 := by
  classical
  convert
      linearData.transported_projection_coordinate linearFullEquiv i (linearFullCoordinate i)
    (fun v => by rw [linearFullEquiv_embedding]; rfl) Subtype.val
    (fun S => ⟨forestHead S,forestHead_contains S⟩) H x using 1
  all_goals congr

lemma quadraticFullHeads_coordinate (H : ForestHead) (x : FullQuadraticSpace) (i : ForestCoord) :
    quadraticFullCoordinate i (quadraticFullHeads.projection H x)=if i ∈ H.val then quadraticFullCoordinate i x else 0 := by
  classical
  convert
      quadraticData.transported_projection_coordinate quadraticFullEquiv i (quadraticFullCoordinate i)
    (fun v => by rw [quadraticFullEquiv_embedding]; rfl) Subtype.val
    (fun S => ⟨forestHead S,forestHead_contains S⟩) H x using 1
  all_goals congr

end PathModel

namespace RecursiveModel
def fullVectorCoordinate : ForestCoord → FullVectorSpace →L[ℝ] ℝ :=
  outerCoordinate (fun h => (fullData (exponent h) (exponent_real_pos h) (h+1)).coordinate)
lemma fullVectorCoordinate_equiv (i : ForestCoord) (x : VectorSpace) :
    fullVectorCoordinate i (fullVectorEquiv x)=vectorData.coordinate i x :=
  vectorData.coordinate_of_equiv fullVectorEquiv i (fullVectorCoordinate i) (fun v => by
    rw [fullVectorEquiv_embedding]
    rfl) x
lemma fullVectorHeads_coordinate (H : ForestHead) (x : FullVectorSpace) (i : ForestCoord) :
    fullVectorCoordinate i (fullVectorHeads.projection H x)=if i ∈ H.val then fullVectorCoordinate i x else 0 := by
  classical
  convert
      vectorData.transported_projection_coordinate fullVectorEquiv i (fullVectorCoordinate i)
    (fun v => by rw [fullVectorEquiv_embedding]; rfl) Subtype.val
    (fun S => ⟨forestHead S,forestHead_contains S⟩) H x using 1
  all_goals congr

end RecursiveModel

namespace StartModel
open RecursiveModel
def componentCoordinate (h : ℕ) (r : Coord h) : FullComponent h →L[ℝ] ℝ :=
  (LinearMap.ker (output h)).liftQL (outputCoordinate h r) (by
    intro d hd
    change output h d r=0
    exact congrFun hd r)
lemma componentCoordinate_rep (h : ℕ) (r : Coord h) (d : Rep h) :
    componentCoordinate h r ((LinearMap.ker (output h)).mkQ d)=output h d r := rfl
lemma componentCoordinate_embedding (h : ℕ) (r : Coord h) (v : Vec h) :
    componentCoordinate h r (componentEmbedding h v)=v r := by
  change output h (finiteSection h v) r=v r
  exact congrFun ((relation h).section_output v) r

def fullCoordinate : ForestCoord → FullSpace →L[ℝ] ℝ :=
  outerCoordinate (fun h => componentCoordinate (h+1))
lemma fullCoordinate_embedding (i : ForestCoord) (v : ForestVec) : fullCoordinate i (fullEmbedding v)=v i :=
  outerCoordinate_embedding _ _ (fun h i v => componentCoordinate_embedding (h+1) i v) i v
lemma fullCoordinate_equiv (i : ForestCoord) (x : Space) :
    fullCoordinate i (fullEquiv x)=data.coordinate i x :=
  data.coordinate_of_equiv fullEquiv i (fullCoordinate i) (fun v => by
    rw [fullEquiv_embedding,fullCoordinate_embedding]) x
lemma fullHeads_coordinate (H : ForestHead) (x : FullSpace) (i : ForestCoord) :
    fullCoordinate i (fullHeads.projection H x)=if i ∈ H.val then fullCoordinate i x else 0 := by
  classical
  convert
      data.transported_projection_coordinate fullEquiv i (fullCoordinate i)
    (fun v => by rw [fullEquiv_embedding,fullCoordinate_embedding]) Subtype.val
    (fun S => ⟨forestHead S,forestHead_contains S⟩) H x using 1
  all_goals congr

end StartModel

end DiamondDistortion

end

end OAI
