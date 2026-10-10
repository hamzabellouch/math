import Mathlib
import OAI.Algebra.FiniteTensor.CohomologyReduction
import OAI.Algebra.FiniteTensor.OddTensors

namespace OAI

/-! Tensor representatives, kernel support and projected operator reduction. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace SuperReduction
variable (C : SuperReduction K V)

 
abbrev Representatives := LinearMap.range C.p

def repProject : V →ₗ[K] Representatives C := C.p.rangeRestrict

def repInclude : Representatives C →ₗ[K] V := (LinearMap.range C.p).subtype

@[simp] theorem repProject_apply (v : V) : (repProject C v : V)=C.p v := rfl
@[simp] theorem repInclude_apply (v : Representatives C) : repInclude C v=(v:V) := rfl

@[simp] theorem project_include (v : Representatives C) : repProject C (repInclude C v)=v := by
  apply Subtype.ext
  obtain ⟨w,hw⟩ := v.property
  change C.p (v:V)=(v:V)
  rw [← hw,C.pp]

@[simp] theorem d_include (v : Representatives C) : C.d (repInclude C v)=0 := by
  obtain ⟨w,hw⟩ := v.property
  change C.d (v:V)=0
  rw [← hw,C.dp]

@[simp] theorem project_d (v : V) : repProject C (C.d v)=0 := by
  apply Subtype.ext
  exact C.pd v

 
theorem project_map_project (f : V →ₗ[K] V)
    (hf : ∀ v, C.p (f (C.d v))=0) (v : V) (hv : C.d v=0) :
    repProject C (f (C.p v))=repProject C (f v) := by
  apply Subtype.ext
  change C.p (f (C.p v))=C.p (f v)
  have h := C.hom v
  rw [hv,map_zero,add_zero] at h
  have hh := congrArg (fun x => C.p (f x)) h
  rw [hf,map_sub,map_sub] at hh
  exact (sub_eq_zero.mp hh.symm).symm

def repMap (f : V →ₗ[K] V) : Representatives C →ₗ[K] Representatives C :=
  (repProject C).comp (f.comp (repInclude C))

@[simp] theorem repMap_apply (f : V →ₗ[K] V) (v : Representatives C) :
    repMap C f v=repProject C (f (v:V)) := rfl

@[simp] theorem repMap_zero : repMap C (0 : V →ₗ[K] V)=0 := by
  apply LinearMap.ext; intro v; simp

@[simp] theorem repMap_id : repMap C (LinearMap.id : V →ₗ[K] V)=LinearMap.id := by
  apply LinearMap.ext; intro v
  exact project_include C v

@[simp] theorem repMap_add (f g : V →ₗ[K] V) : repMap C (f+g)=repMap C f+repMap C g := by
  apply LinearMap.ext; intro v; simp

@[simp] theorem repMap_neg (f : V →ₗ[K] V) : repMap C (-f) = -repMap C f := by
  apply LinearMap.ext; intro v; simp

 
theorem repMap_comp (f g : V →ₗ[K] V)
    (hf : ∀ v, C.p (f (C.d v))=0)
    (hg : ∀ v, C.d v=0 → C.d (g v)=0) :
    (repMap C f).comp (repMap C g)=repMap C (f.comp g) := by
  apply LinearMap.ext; intro v
  change repProject C (f (C.p (g (v:V))))=repProject C (f (g (v:V)))
  exact project_map_project C f hf _ (hg _ (d_include C v))

 

theorem exists_induced_reduction [Invertible (2:K)]
    (d b g : V →ₗ[K] V)
    (hdd : ∀ v, d (d v)=0) (hgg : ∀ v, g (g v)=v)
    (hdg : ∀ v, d (g v) = -g (d v))
    (hδd : ∀ v, C.d (d v) = -d (C.d v))
    (hδg : ∀ v, C.d (g v) = -g (C.d v))
    (hδb : ∀ v, C.d (b v) = b (C.d v))
    (hbg : ∀ v, b (g v)=g (b v)) :
    ∃ E : SuperReduction K (Representatives C),
      E.d=repMap C d ∧ E.g=repMap C g ∧
      ∀ v, repMap C b v=0 → repMap C b (E.p v)=0 := by
  have dcycle : ∀ v, C.d v=0 → C.d (d v)=0 := by
    intro v hv; rw [hδd,hv,map_zero,neg_zero]
  have gcycle : ∀ v, C.d v=0 → C.d (g v)=0 := by
    intro v hv; rw [hδg,hv,map_zero,neg_zero]
  have bcycle : ∀ v, C.d v=0 → C.d (b v)=0 := by
    intro v hv; rw [hδb,hv,map_zero]
  have dbound : ∀ v, C.p (d (C.d v))=0 := by
    intro v
    have h := congrArg C.p (hδd v)
    rw [C.pd,map_neg] at h
    exact neg_eq_zero.mp h.symm
  have gbound : ∀ v, C.p (g (C.d v))=0 := by
    intro v
    have h := congrArg C.p (hδg v)
    rw [C.pd,map_neg] at h
    exact neg_eq_zero.mp h.symm
  have bbound : ∀ v, C.p (b (C.d v))=0 := by
    intro v
    have h := congrArg C.p (hδb v)
    rw [C.pd] at h
    exact h.symm
  have dd : ∀ v, repMap C d (repMap C d v)=0 := by
    have hh : d.comp d=0 := LinearMap.ext hdd
    intro v
    have h := LinearMap.congr_fun (repMap_comp C d d dbound dcycle) v
    simpa only [LinearMap.comp_apply,hh,repMap_zero,LinearMap.zero_apply] using h
  have gg : ∀ v, repMap C g (repMap C g v)=v := by
    have hh : g.comp g=LinearMap.id := LinearMap.ext hgg
    intro v
    have h := LinearMap.congr_fun (repMap_comp C g g gbound gcycle) v
    simpa only [LinearMap.comp_apply,hh,repMap_id,LinearMap.id_apply] using h
  have dg : ∀ v, repMap C d (repMap C g v) = -repMap C g (repMap C d v) := by
    have hh : d.comp g= -(g.comp d) := LinearMap.ext hdg
    intro v
    have h₁ := LinearMap.congr_fun (repMap_comp C d g dbound gcycle) v
    have h₂ := LinearMap.congr_fun (repMap_comp C g d gbound dcycle) v
    rw [hh,repMap_neg] at h₁
    exact h₁.trans (congrArg Neg.neg h₂.symm)
  have bg : ∀ v, repMap C b (repMap C g v)=repMap C g (repMap C b v) := by
    have hh : b.comp g=g.comp b := LinearMap.ext hbg
    intro v
    have h₁ := LinearMap.congr_fun (repMap_comp C b g bbound gcycle) v
    have h₂ := LinearMap.congr_fun (repMap_comp C g b gbound bcycle) v
    exact h₁.trans (hh ▸ h₂.symm)
  obtain ⟨E,hEd,hEg,hEp⟩ := exists_superReduction (repMap C d) (repMap C g)
    dd gg dg (LinearMap.ker (repMap C b)) (by
      intro v hv
      change repMap C b (repMap C g v)=0
      rw [bg,hv,map_zero])
  exact ⟨E,hEd,hEg,hEp⟩

end SuperReduction
end
end PD4Tensor

 

namespace PD4Tensor
noncomputable section
open scoped TensorProduct

variable {K V W X : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup X] [Module K X]

 
theorem factor_of_ker_le (f : V →ₗ[K] W) (g : V →ₗ[K] X)
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ l : W →ₗ[K] X, l.comp f = g := by
  let a : LinearMap.range f →ₗ[K] X :=
    ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨l, hl⟩ := a.exists_extend
  refine ⟨l, ?_⟩
  ext v
  have hv := LinearMap.congr_fun hl ⟨f v, LinearMap.mem_range_self f v⟩
  simpa [a] using hv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

 
def partialTensor (b : ∀ i, E i →ₗ[K] E i) (S : Finset ι) :
    (⨂[K] i, E i) →ₗ[K] (⨂[K] i, E i) :=
  PiTensorProduct.map (fun i => if i ∈ S then b i else LinearMap.id)

 
def kernelSupport (b : ∀ i, E i →ₗ[K] E i) (r : ℕ) :
    Submodule K (⨂[K] i, E i) :=
  Submodule.span K {v | ∃ (f : ∀ i, E i) (S : Finset ι),
    S.card ≤ r ∧ (∀ i ∉ S, b i (f i) = 0) ∧ PiTensorProduct.tprod K f = v}

 
theorem triple_kernel_support (b : ∀ i, E i →ₗ[K] E i)
    (v : ⨂[K] i, E i)
    (hv : ∀ S : Finset ι, S.card = 3 → partialTensor E b S v = 0) :
    v ∈ kernelSupport E b 2 := by
  classical
  
  choose C hC using fun i => (LinearMap.ker (b i)).exists_isCompl
  let P : ∀ i, E i →ₗ[K] E i := fun i =>
    (LinearMap.ker (b i)).subtype.comp
      ((LinearMap.ker (b i)).projectionOnto (C i) (hC i))
  let Q : ∀ i, E i →ₗ[K] E i := fun i => LinearMap.id - P i
  have hP (i : ι) (x : E i) : b i (P i x) = 0 :=
    ((LinearMap.ker (b i)).projectionOnto (C i) (hC i) x).property
  have hQ (i : ι) : LinearMap.ker (b i) ≤ LinearMap.ker (Q i) := by
    intro x hx
    simp only [LinearMap.mem_ker, Q, LinearMap.sub_apply, LinearMap.id_apply]
    change x - ((LinearMap.ker (b i)).projectionOnto (C i) (hC i) x : E i) = 0
    rw [Submodule.projectionOnto_apply_of_mem_left (hC i) hx]
    exact sub_self _
  choose L hL using fun i => factor_of_ker_le (b i) (Q i) (hQ i)
  have hsum : (∑ S : Finset ι, PiTensorProduct.map (S.piecewise Q P)) =
      (LinearMap.id : (⨂[K] i, E i) →ₗ[K] (⨂[K] i, E i)) := by
    have h := (PiTensorProduct.mapMultilinear K E E).map_add_univ Q P
    have hQP : Q + P = fun i => LinearMap.id := by
      funext i
      simp [Q]
    rw [hQP] at h
    exact h.symm.trans PiTensorProduct.map_id
  have hsmall (S : Finset ι) (hS : S.card ≤ 2) :
      PiTensorProduct.map (S.piecewise Q P) v ∈ kernelSupport E b 2 := by
    have hrange : LinearMap.range (PiTensorProduct.map (S.piecewise Q P)) ≤
        kernelSupport E b 2 := by
      rw [PiTensorProduct.map_range_eq_span_tprod]
      apply Submodule.span_le.mpr
      rintro z ⟨f, rfl⟩
      apply Submodule.subset_span
      refine ⟨fun i => S.piecewise Q P i (f i), S, hS, ?_, rfl⟩
      intro i hi
      simpa [Finset.piecewise, hi] using hP i (f i)
    exact hrange (LinearMap.mem_range_self _ v)
  have hlarge (S : Finset ι) (hS : 2 < S.card) :
      PiTensorProduct.map (S.piecewise Q P) v = 0 := by
    obtain ⟨R, hRS, hR⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
    let D : ∀ i, E i →ₗ[K] E i := fun i =>
      if i ∈ R then L i else S.piecewise Q P i
    have hfactor : PiTensorProduct.map (S.piecewise Q P) =
        (PiTensorProduct.map D).comp (partialTensor E b R) := by
      rw [partialTensor, ← PiTensorProduct.map_comp]
      congr 1
      funext i
      by_cases hi : i ∈ R
      · simpa [D, Finset.piecewise, hi, hRS hi] using (hL i).symm
      · simp [D, hi]
    rw [hfactor, LinearMap.comp_apply, hv R hR, map_zero]
  have heq := LinearMap.congr_fun hsum v
  rw [LinearMap.sum_apply, LinearMap.id_apply] at heq
  rw [← heq]
  apply Submodule.sum_mem
  intro S _
  by_cases hS : S.card ≤ 2
  · exact hsmall S hS
  · rw [hlarge S (by omega)]
    exact Submodule.zero_mem _

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped TensorProduct
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace SuperReduction

 
theorem cycle_of_project_zero (C : SuperReduction K V) (v : V)
    (hd : C.d v=0) (hp : repProject C v=0) : v ∈ LinearMap.range C.d := by
  refine ⟨C.h v, ?_⟩
  have h := C.hom v
  have hp' : C.p v=0 := congrArg Subtype.val hp
  simpa only [hd,hp',map_zero,add_zero,sub_zero] using h

end SuperReduction

namespace CohomologyTensor
open SuperReduction
variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
variable (C : ∀ i, SuperReduction K (E i))

abbrev Factors (i : ι) := Representatives (C i)

def project : (⨂[K] i, E i) →ₗ[K] (⨂[K] i, Factors C i) :=
  PiTensorProduct.map (fun i => repProject (C i))

def embed : (⨂[K] i, Factors C i) →ₗ[K] (⨂[K] i, E i) :=
  PiTensorProduct.map (fun i => repInclude (C i))

omit [Fintype ι] [LinearOrder ι] in
@[simp] theorem project_include (v : ⨂[K] i, Factors C i) : project C (embed C v)=v := by
  have h : (project C).comp (embed C)=LinearMap.id := by
    rw [project,embed,← PiTensorProduct.map_comp]
    have hmap : (fun i => (repProject (C i)).comp (repInclude (C i))) =
        fun i => (LinearMap.id : Factors C i →ₗ[K] Factors C i) := by
      funext i
      apply LinearMap.ext; intro v
      exact SuperReduction.project_include (C i) v
    rw [hmap,PiTensorProduct.map_id]
  exact LinearMap.congr_fun h v

omit [Fintype ι] [LinearOrder ι] in
@[simp] theorem include_project (v : ⨂[K] i, E i) : embed C (project C v)=finiteP C v := by
  have h : (embed C).comp (project C)=finiteP C := by
    rw [embed,project,← PiTensorProduct.map_comp]
    rfl
  exact LinearMap.congr_fun h v

theorem finiteD_eq : finiteD C=oddTensor (fun i => (C i).g) (fun i => (C i).d) := rfl

@[simp] theorem project_d (v : ⨂[K] i, E i) : project C (finiteD C v)=0 := by
  exact LinearMap.congr_fun (tensorMap_oddTensor_zero (fun i => (C i).g)
    (fun i => (C i).d) (fun i => repProject (C i)) (fun i => SuperReduction.project_d (C i))) v

@[simp] theorem d_include (v : ⨂[K] i, Factors C i) : finiteD C (embed C v)=0 := by
  exact LinearMap.congr_fun (oddTensor_tensorMap_zero (fun i => (C i).g)
    (fun i => (C i).d) (fun i => repInclude (C i)) (fun i => SuperReduction.d_include (C i))) v

 
theorem odd_sandwich (d : ∀ i, E i →ₗ[K] E i) (v : ⨂[K] i, Factors C i) :
    project C (oddTensor (fun i => (C i).g) d (embed C v)) =
    oddTensor (fun i => repMap (C i) (C i).g) (fun i => repMap (C i) (d i)) v := by
  exact LinearMap.congr_fun (oddTensor_sandwich (fun i => (C i).g) d
    (fun i => repProject (C i)) (fun i => repInclude (C i))
    (fun i => SuperReduction.project_include (C i))) v

 
omit [Fintype ι] in
theorem partial_sandwich (b : ∀ i, E i →ₗ[K] E i) (S : Finset ι)
    (v : ⨂[K] i, Factors C i) :
    project C (partialTensor E b S (embed C v)) =
      partialTensor (fun i => ↥(Factors C i)) (fun i => repMap (C i) (b i)) S v := by
  have h : (project C).comp ((partialTensor E b S).comp (embed C)) =
      partialTensor (fun i => ↥(Factors C i)) (fun i => repMap (C i) (b i)) S := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [project,embed,partialTensor,LinearMap.compMultilinearMap_apply,
      LinearMap.comp_apply,PiTensorProduct.map_tprod]
    congr 1
    funext i
    by_cases hi : i∈S
    · simp only [hi,ite_true,repMap_apply,repInclude_apply]
    · simp only [hi,ite_false,LinearMap.id_apply,SuperReduction.project_include]
  exact LinearMap.congr_fun h v

 
theorem partial_commute (b : ∀ i, E i →ₗ[K] E i)
    (hbd : ∀ i v, b i ((C i).d v)=(C i).d (b i v))
    (hbg : ∀ i v, b i ((C i).g v)=(C i).g (b i v))
    (S : Finset ι) (v : ⨂[K] i, E i) :
    partialTensor E b S (finiteD C v)=finiteD C (partialTensor E b S v) := by
  apply LinearMap.congr_fun (oddTensor_naturality (fun i => (C i).g) (fun i => (C i).d)
    (fun i => (C i).g) (fun i => (C i).d) (fun i => if i∈S then b i else LinearMap.id) ?_ ?_) v
  · intro i w; by_cases hi : i∈S <;> simp [hi,hbg]
  · intro i w; by_cases hi : i∈S <;> simp [hi,hbd]

 

theorem pairing_projection (L : (⨂[K] i, E i) →ₗ[K] K)
    (hL : ∀ v, L (finiteD C v)=0) (v : ⨂[K] i, E i) (hv : finiteD C v=0) :
    L (embed C (project C v))=L v := by
  obtain ⟨w,hw⟩ := finite_cycle_mod_projection C v hv
  have hh := congrArg L hw
  rw [hL,map_sub] at hh
  rw [include_project]
  exact (sub_eq_zero.mp hh.symm).symm

 

theorem operator_projection (f : (⨂[K] i, E i) →ₗ[K] (⨂[K] i, E i))
    (hf : ∀ v, project C (f (finiteD C v))=0)
    (v : ⨂[K] i, E i) (hv : finiteD C v=0) :
    project C (f (embed C (project C v)))=project C (f v) := by
  obtain ⟨w,hw⟩ := finite_cycle_mod_projection C v hv
  have hh := congrArg (fun z => project C (f z)) hw
  rw [hf,map_sub,map_sub] at hh
  rw [include_project]
  exact (sub_eq_zero.mp hh.symm).symm

end CohomologyTensor
end
end PD4Tensor
end

end OAI
