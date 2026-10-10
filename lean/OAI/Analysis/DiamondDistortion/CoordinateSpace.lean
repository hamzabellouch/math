import OAI.Analysis.DiamondDistortion.PathBounds

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace CoordinateCompletion
variable {ι : Type*}

/-- A specified coordinate norm, with individually bounded coordinate evaluations.
    No bound on the norms of coordinate projections is imposed. -/
structure Data (ι : Type*) where
  seminorm : Seminorm ℝ (ι →₀ ℝ)
  coordinate_bound : ∀ i,∃ C : ℝ,∀ v,|v i| ≤ C*seminorm v

namespace Data
variable (A : Data ι)
lemma separates (v : ι →₀ ℝ) (hv : A.seminorm v=0) : v=0 := by
  ext i
  obtain ⟨C,hC⟩ := A.coordinate_bound i
  have hh := hC v
  rw [hv,mul_zero] at hh
  exact abs_nonpos_iff.mp hh

def Finite (_A : Data ι) := ι →₀ ℝ
instance : AddCommGroup A.Finite := inferInstanceAs (AddCommGroup (ι →₀ ℝ))
instance : Module ℝ A.Finite := inferInstanceAs (Module ℝ (ι →₀ ℝ))
instance : NormedAddCommGroup A.Finite := AddGroupNorm.toNormedAddCommGroup
  { A.seminorm.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := A.separates }
instance : NormedSpace ℝ A.Finite where
  norm_smul_le t v := le_of_eq (A.seminorm.smul' t v)
abbrev Space := UniformSpace.Completion A.Finite

def finite (v : ι →₀ ℝ) : A.Finite := v
def array (v : A.Finite) : ι →₀ ℝ := v
def embedding : (ι →₀ ℝ) →ₗ[ℝ] A.Space :=
  (UniformSpace.Completion.toComplL (S := ℝ) (α := A.Finite)).toLinearMap
@[simp] lemma norm_embedding (v : ι →₀ ℝ) : ‖A.embedding v‖=A.seminorm v :=
  UniformSpace.Completion.norm_coe _

def coordinateFinite (i : ι) : A.Finite →L[ℝ] ℝ :=
  (show A.Finite →ₗ[ℝ] ℝ from Finsupp.lapply i).mkContinuous
    (A.coordinate_bound i).choose (by
      intro v
      change ‖(show ι →₀ ℝ from v) i‖ ≤ (A.coordinate_bound i).choose*A.seminorm v
      simpa only [Real.norm_eq_abs] using (A.coordinate_bound i).choose_spec v)
def coordinate (i : ι) : A.Space →L[ℝ] ℝ :=
  (A.coordinateFinite i).extend UniformSpace.Completion.toComplL
@[simp] lemma coordinate_coe (i : ι) (v : A.Finite) : A.coordinate i (v : A.Space)=A.array v i :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) v
@[simp] lemma coordinate_embedding (i : ι) (v : ι →₀ ℝ) : A.coordinate i (A.embedding v)=v i :=
  A.coordinate_coe i (A.finite v)
def unit (i : ι) : A.Space := A.embedding (Finsupp.single i 1)
@[simp] lemma coordinate_unit (i j : ι) : A.coordinate i (A.unit j)=if j=i then 1 else 0 := by
  simp [unit,Finsupp.single_apply]

def projection (H : Finset ι) : A.Space →L[ℝ] A.Space :=
  ∑ i ∈ H,(A.coordinate i).smulRight (A.unit i)
@[simp] lemma projection_apply (H : Finset ι) (x : A.Space) :
    A.projection H x=∑ i ∈ H,A.coordinate i x • A.unit i := by simp [projection]
@[simp] lemma coordinate_projection (H : Finset ι) (x : A.Space) (i : ι) :
    A.coordinate i (A.projection H x)=if i ∈ H then A.coordinate i x else 0 := by
  simp [projection_apply,map_sum,map_smul,smul_eq_mul,mul_ite,Finset.sum_ite_eq']
lemma projection_idempotent (H : Finset ι) (x : A.Space) :
    A.projection H (A.projection H x)=A.projection H x := by
  rw [A.projection_apply H (A.projection H x)]
  simp only [coordinate_projection]
  rw [projection_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left hi]
lemma projection_commutes (H K : Finset ι) (x : A.Space) :
    A.projection H (A.projection K x)=A.projection K (A.projection H x) := by
  rw [A.projection_apply H (A.projection K x),
    A.projection_apply K (A.projection H x)]
  simp only [coordinate_projection,ite_smul,zero_smul]
  rw [← Finset.sum_filter,← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter,and_comm]

def headMap (H : Finset ι) : (H → ℝ) →ₗ[ℝ] A.Space where
  toFun a := ∑ i : H,a i • A.unit i
  map_add' a b := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' t a := by simp [Pi.smul_apply,smul_smul,Finset.smul_sum]
lemma projection_range (H : Finset ι) : LinearMap.range (A.projection H).toLinearMap ≤
    LinearMap.range (A.headMap H) := by
  rintro x ⟨y,rfl⟩
  refine ⟨fun i => A.coordinate i y,?_⟩
  change (∑ i : H,A.coordinate i y • A.unit i)=A.projection H y
  rw [projection_apply]
  exact Finset.sum_attach H (fun i => A.coordinate i y • A.unit i)

lemma projection_finite (H : Finset ι) : FiniteDimensional ℝ (LinearMap.range (A.projection H).toLinearMap) := by
  let : FiniteDimensional ℝ (LinearMap.range (A.headMap H)) := Module.Finite.range (A.headMap H)
  exact Submodule.finiteDimensional_of_le (A.projection_range H)

lemma projection_embedding (H : Finset ι) (v : ι →₀ ℝ) :
    A.projection H (A.embedding v)=A.embedding (v.filter (· ∈ H)) := by
  rw [projection_apply]
  simp only [coordinate_embedding,unit]
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext i
  simp [Finsupp.single_apply,Finsupp.filter_apply,Finset.sum_ite_eq']

lemma finite_fixed (v : ι →₀ ℝ) {H : Finset ι} (hH : v.support ⊆ H) :
    A.projection H (A.embedding v)=A.embedding v := by
  rw [projection_embedding]
  congr 1
  ext i
  rw [Finsupp.filter_apply]
  split_ifs with hi
  · rfl
  · exact (Finsupp.notMem_support_iff.mp (fun hv => hi (hH hv))).symm

lemma approximation (x : A.Space) {η : ℝ} (hη : 0 < η) :
    ∃ v : ι →₀ ℝ,‖x-A.embedding v‖ < η := by
  obtain ⟨v,hv⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hη
  refine ⟨A.array v,?_⟩
  change ‖x-(v : A.Space)‖ < η
  simpa only [dist_eq_norm] using hv

end Data
end CoordinateCompletion

namespace CoordinateCompletion.Data
variable {ι κ : Type*} (A : CoordinateCompletion.Data ι)

def heads (H : κ → Finset ι) (hcover : ∀ S : Finset ι,∃ h,S ⊆ H h) : Midpoint.Heads κ A.Space where
  projection h := A.projection (H h)
  idempotent h := A.projection_idempotent (H h)
  finite h := A.projection_finite (H h)
  approximation x η hη := by
    obtain ⟨v,hv⟩ := A.approximation x hη
    obtain ⟨h,hh⟩ := hcover v.support
    exact ⟨h,A.embedding v,A.finite_fixed v hh,hv⟩
lemma heads_commutes (H : κ → Finset ι) (hcover : ∀ S : Finset ι,∃ h,S ⊆ H h) :
    (A.heads H hcover).Commutes := by
  intro i j x
  exact A.projection_commutes (H i) (H j) x

/-- Every vector fixed by a finite head is an actual finite coordinate vector. -/
lemma projection_eq_embedding (H : Finset ι) (x : A.Space) :
    ∃ v : ι →₀ ℝ,A.projection H x=A.embedding v := by
  refine ⟨∑ i ∈ H,(A.coordinate i x) • Finsupp.single i 1,?_⟩
  rw [projection_apply,map_sum]
  simp only [map_smul,unit]
lemma fixed_finite {H : Finset ι} {x : A.Space} (hx : A.projection H x=x) :
    ∃ v : ι →₀ ℝ,x=A.embedding v := by
  obtain ⟨v,hv⟩ := A.projection_eq_embedding H x
  exact ⟨v,hx ▸ hv⟩

end CoordinateCompletion.Data

end DiamondDistortion

end

end OAI
