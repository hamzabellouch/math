import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.VectorBundle.Basic

namespace OAI

noncomputable section

/-! Finite direct sums of line bundles, metrics, inclusions, and projections. -/

section
open Bundle Topology
open scoped BigOperators
namespace Kaplansky

variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

/-- The simultaneous finite cover for the direct sum of actual line cores. -/
def lineSumBaseSet (a : ∀ s, J s) : Set B := {x | ∀ s, x ∈ (C s).baseSet (a s)}

theorem isOpen_lineSumBaseSet (a : ∀ s, J s) : IsOpen (lineSumBaseSet C a) := by
  have he : lineSumBaseSet C a = ⋂ s, (C s).baseSet (a s) := by
    ext x
    simp [lineSumBaseSet]
  rw [he]
  exact isOpen_iInter_of_finite (fun s => (C s).isOpen_baseSet (a s))

/-- Componentwise transition on the finite Hilbert direct sum. -/
def lineSumTransition (a b : ∀ s, J s) (x : B) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  (EuclideanSpace.equiv S ℂ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun s =>
      ((C s).coordChange (a s) (b s) x).comp (ContinuousLinearMap.proj s))).comp
      (EuclideanSpace.equiv S ℂ).toContinuousLinearMap)

omit [Fintype S] in
@[simp] theorem lineSumTransition_apply (a b : ∀ s, J s) (x : B)
    (v : EuclideanSpace ℂ S) (s : S) :
    lineSumTransition C a b x v s = (C s).coordChange (a s) (b s) x (v s) := rfl

theorem continuousOn_lineSumTransition (a b : ∀ s, J s) :
    ContinuousOn (lineSumTransition C a b) (lineSumBaseSet C a ∩ lineSumBaseSet C b) := by
  apply continuousOn_clm_apply.mpr
  intro v
  apply (EuclideanSpace.equiv S ℂ).symm.continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  exact (((C s).continuousOn_coordChange (a s) (b s)).mono
    (fun x hx => ⟨hx.1 s,hx.2 s⟩)).clm_apply continuousOn_const

/-- A finite direct sum, with its ordinary vector-bundle topology and
finite Hilbert-space fibers. Neither a trivialization nor a trivial bundle
is asserted by the fact that the core uses a fixed model fiber. -/
def finiteLineSumCore : VectorBundleCore ℂ B (EuclideanSpace ℂ S) (∀ s, J s) where
  baseSet := lineSumBaseSet C
  isOpen_baseSet := isOpen_lineSumBaseSet C
  indexAt x s := (C s).indexAt x
  mem_baseSet_at x s := (C s).mem_baseSet_at x
  coordChange := lineSumTransition C
  coordChange_self a x hx v := by
    ext s
    exact (C s).coordChange_self (a s) x (hx s) (v s)
  continuousOn_coordChange := continuousOn_lineSumTransition C
  coordChange_comp a b c x hx v := by
    ext s
    exact (C s).coordChange_comp (a s) (b s) (c s) x
      ⟨⟨hx.1.1 s,hx.1.2 s⟩,hx.2 s⟩ (v s)

/-- The direct sum has the actual line-core fibers as its components. -/
def finiteLineSumFiberEquiv (x : B) :
    (finiteLineSumCore C).Fiber x ≃ₗ[ℂ] (∀ s, (C s).Fiber x) :=
  (EuclideanSpace.equiv S ℂ).toLinearEquiv

theorem finiteLineSum_finrank (x : B) :
    Module.finrank ℂ ((finiteLineSumCore C).Fiber x) = Fintype.card S := by
  change Module.finrank ℂ (EuclideanSpace ℂ S) = _
  simp

/-- In every simultaneous chart, components agree with the individual
line-bundle charts, which identifies the direct-sum gluing explicitly. -/
theorem finiteLineSum_chart_component (a : ∀ s, J s) (x : B)
    (v : (finiteLineSumCore C).Fiber x) (s : S) :
    (((finiteLineSumCore C).localTriv a) ⟨x,v⟩).2 s =
      (((C s).localTriv (a s)) ⟨x,finiteLineSumFiberEquiv C x v s⟩).2 := rfl

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

def finiteLineSumComponent (s : S)
    (z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber) :
    TotalSpace ℂ (C s).Fiber := ⟨z.proj, finiteLineSumFiberEquiv C z.proj z.2 s⟩

theorem continuous_finiteLineSumComponent (s : S) :
    Continuous (finiteLineSumComponent C s) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  constructor
  · exact (FiberBundle.continuous_proj _ _).continuousAt
  · let a : ∀ s, J s := (finiteLineSumCore C).indexAt z.proj
    have hz : z ∈ ((finiteLineSumCore C).localTriv a).source :=
      ((finiteLineSumCore C).localTriv a).mem_source.mpr
        ((finiteLineSumCore C).mem_baseSet_at z.proj)
    have h := (((finiteLineSumCore C).localTriv a).continuousAt hz).snd
    exact ((continuous_apply s).comp (EuclideanSpace.equiv S ℂ).continuous).continuousAt.comp h

/-- Continuity into the actual finite sum is exactly continuity of its
base and all of its actual line-bundle components. This includes the empty sum. -/
theorem continuous_finiteLineSum_iff {X : Type*} [TopologicalSpace X]
    (f : X → TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber) :
    Continuous f ↔ Continuous (fun x => (f x).proj) ∧
      ∀ s, Continuous (fun x => finiteLineSumComponent C s (f x)) := by
  constructor
  · intro hf
    exact ⟨(FiberBundle.continuous_proj _ _).comp hf,
      fun s => (continuous_finiteLineSumComponent C s).comp hf⟩
  · rintro ⟨hb,hc⟩
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    have h : ContinuousAt (fun y s =>
        (trivializationAt ℂ (C s).Fiber (f x).proj
          (finiteLineSumComponent C s (f y))).2) x := by
      apply continuousAt_pi.mpr
      intro s
      exact (FiberBundle.continuousAt_totalSpace ℂ _).mp ((hc s).continuousAt) |>.2
    exact (EuclideanSpace.equiv S ℂ).symm.continuous.continuousAt.comp h

end Kaplansky

open Bundle Topology
open scoped BigOperators InnerProductSpace
namespace Kaplansky
variable {B S : Type*} [TopologicalSpace B] [Fintype S]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))

instance finiteLineSumFiberNormedAddCommGroup (x : B) :
    NormedAddCommGroup ((finiteLineSumCore C).Fiber x) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ S))

instance finiteLineSumFiberInnerProductSpace (x : B) :
    InnerProductSpace ℂ ((finiteLineSumCore C).Fiber x) :=
  inferInstanceAs (InnerProductSpace ℂ (EuclideanSpace ℂ S))

/-- The ordinary isometry condition on the given line-bundle transitions. -/
def LineCoreIsUnitary : Prop := ∀ s a b x,
  x ∈ (C s).baseSet a → x ∈ (C s).baseSet b → ∀ z w : ℂ,
  inner ℂ ((C s).coordChange a b x z) ((C s).coordChange a b x w) = inner ℂ z w

theorem finiteLineSumTransition_inner (hC : LineCoreIsUnitary C)
    (a b : ∀ s, J s) (x : B) (ha : x ∈ lineSumBaseSet C a)
    (hb : x ∈ lineSumBaseSet C b) (v w : EuclideanSpace ℂ S) :
    inner ℂ (lineSumTransition C a b x v) (lineSumTransition C a b x w) = inner ℂ v w := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro s _
  exact hC s (a s) (b s) x (ha s) (hb s) (v s) (w s)

theorem finiteLineSum_chart_inner (hC : LineCoreIsUnitary C)
    (a : ∀ s, J s) (x : B) (ha : x ∈ lineSumBaseSet C a)
    (v w : (finiteLineSumCore C).Fiber x) :
    inner ℂ (((finiteLineSumCore C).localTriv a) ⟨x,v⟩).2
      (((finiteLineSumCore C).localTriv a) ⟨x,w⟩).2 = inner ℂ v w :=
  finiteLineSumTransition_inner C hC _ a x ((finiteLineSumCore C).mem_baseSet_at x) ha v w

/-- The fiberwise Hilbert metrics are continuous on the constructed bundle,
proved in local charts. This is the continuous Hermitian metric condition
for arbitrary continuous local sections. -/
theorem finiteLineSum_inner_continuousOn (hC : LineCoreIsUnitary C)
    (A : Set B) (v w : ∀ x, (finiteLineSumCore C).Fiber x)
    (hv : ContinuousOn (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) x (v x)) A)
    (hw : ContinuousOn (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) x (w x)) A) :
    ContinuousOn (fun x => inner ℂ (v x) (w x)) A := by
  intro x hx
  let a := (finiteLineSumCore C).indexAt x
  have hax : x ∈ lineSumBaseSet C a := (finiteLineSumCore C).mem_baseSet_at x
  have hcv := ((FiberBundle.continuousWithinAt_totalSpace (EuclideanSpace ℂ S) _).mp (hv x hx)).2
  have hcw := ((FiberBundle.continuousWithinAt_totalSpace (EuclideanSpace ℂ S) _).mp (hw x hx)).2
  apply (hcv.inner hcw).congr_of_eventuallyEq
  · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((isOpen_lineSumBaseSet C a).mem_nhds hax)] with y hy
    exact (finiteLineSum_chart_inner C hC a y hy (v y) (w y)).symm
  · exact (finiteLineSum_chart_inner C hC a x hax (v x) (w x)).symm

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S⊕T → Type*} (L : ∀ u, VectorBundleCore ℂ B ℂ (J u))

def lineSumInl (x : B) : (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber x →ₗ[ℂ]
    (finiteLineSumCore L).Fiber x where
  toFun v := WithLp.toLp 2 (Sum.elim (fun s => (show EuclideanSpace ℂ S from v) s) (fun _ => 0))
  map_add' v w := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => rfl
    | inr t => exact (zero_add (0 : ℂ)).symm
  map_smul' z v := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => rfl
    | inr t => exact (smul_zero z : z • (0 : ℂ) = 0).symm

def lineSumInr (x : B) : (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber x →ₗ[ℂ]
    (finiteLineSumCore L).Fiber x where
  toFun v := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun t => (show EuclideanSpace ℂ T from v) t))
  map_add' v w := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => exact (zero_add (0 : ℂ)).symm
    | inr t => rfl
  map_smul' z v := by
    apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
    funext u
    cases u with
    | inl s => exact (smul_zero z : z • (0 : ℂ) = 0).symm
    | inr t => rfl

theorem lineSumInl_injective (x : B) : Function.Injective (lineSumInl L x) := by
  intro v w h
  apply (EuclideanSpace.equiv S ℂ).injective
  funext s
  exact congrArg (fun u : EuclideanSpace ℂ (S⊕T) => u (Sum.inl s)) h

theorem lineSumInr_injective (x : B) : Function.Injective (lineSumInr L x) := by
  intro v w h
  apply (EuclideanSpace.equiv T ℂ).injective
  funext t
  exact congrArg (fun u : EuclideanSpace ℂ (S⊕T) => u (Sum.inr t)) h

theorem continuous_lineSumInl : Continuous (fun z : TotalSpace (EuclideanSpace ℂ S)
    (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber => TotalSpace.mk' (EuclideanSpace ℂ (S⊕T)) z.proj (lineSumInl L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _,?_⟩
  intro u
  cases u with
  | inl s => exact continuous_finiteLineSumComponent (fun s => L (Sum.inl s)) s
  | inr t =>
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,?_⟩
    change ContinuousAt (fun x : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber =>
      (L (Sum.inr t)).coordChange ((L (Sum.inr t)).indexAt x.proj) ((L (Sum.inr t)).indexAt z.proj) x.proj 0) z
    simpa only [map_zero] using (continuousAt_const : ContinuousAt (fun _ : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber => (0 : ℂ)) z)

theorem continuous_lineSumInr : Continuous (fun z : TotalSpace (EuclideanSpace ℂ T)
    (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber => TotalSpace.mk' (EuclideanSpace ℂ (S⊕T)) z.proj (lineSumInr L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  refine ⟨FiberBundle.continuous_proj _ _,?_⟩
  intro u
  cases u with
  | inr t => exact continuous_finiteLineSumComponent (fun t => L (Sum.inr t)) t
  | inl s =>
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj _ _).continuousAt,?_⟩
    change ContinuousAt (fun x : TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber =>
      (L (Sum.inl s)).coordChange ((L (Sum.inl s)).indexAt x.proj) ((L (Sum.inl s)).indexAt z.proj) x.proj 0) z
    simpa only [map_zero] using (continuousAt_const : ContinuousAt (fun _ : TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber => (0 : ℂ)) z)

end Kaplansky

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S → Type*} (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (e : T ≃ S)

def lineSumReindex (x : B) : (finiteLineSumCore (fun t => C (e t))).Fiber x ≃ₗ[ℂ]
    (finiteLineSumCore C).Fiber x where
  toFun v := WithLp.toLp 2 (fun s => (show EuclideanSpace ℂ T from v) (e.symm s))
  invFun v := WithLp.toLp 2 (fun t => (show EuclideanSpace ℂ S from v) (e t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    apply (EuclideanSpace.equiv T ℂ).injective
    funext t
    exact congrArg (fun t => (show EuclideanSpace ℂ T from v) t) (e.symm_apply_apply t)
  right_inv v := by
    apply (EuclideanSpace.equiv S ℂ).injective
    funext s
    exact congrArg (fun s => (show EuclideanSpace ℂ S from v) s) (e.apply_symm_apply s)

def lineSumReindexTotalHomeomorph :
    TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => C (e t))).Fiber ≃ₜ
      TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber where
  toFun z := ⟨z.proj,lineSumReindex C e z.proj z.2⟩
  invFun z := ⟨z.proj,(lineSumReindex C e z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp
  continuous_toFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨FiberBundle.continuous_proj _ _,?_⟩
    intro s
    obtain ⟨t,rfl⟩ := e.surjective s
    change Continuous (fun z : TotalSpace (EuclideanSpace ℂ T) (finiteLineSumCore (fun t => C (e t))).Fiber =>
      TotalSpace.mk' ℂ (E := (C (e t)).Fiber) z.proj ((show EuclideanSpace ℂ T from z.2) (e.symm (e t))))
    simp only [Equiv.symm_apply_apply]
    exact continuous_finiteLineSumComponent (fun t => C (e t)) t
  continuous_invFun := by
    apply (continuous_finiteLineSum_iff _ _).mpr
    refine ⟨FiberBundle.continuous_proj _ _,?_⟩
    intro t
    exact continuous_finiteLineSumComponent C (e t)

theorem lineSumReindex_inner (x : B)
    (v w : (finiteLineSumCore (fun t => C (e t))).Fiber x) :
    inner ℂ (lineSumReindex C e x v) (lineSumReindex C e x w) = inner ℂ v w := by
  change (∑ s : S, inner ℂ ((show EuclideanSpace ℂ T from v) (e.symm s))
    ((show EuclideanSpace ℂ T from w) (e.symm s))) =
    ∑ t : T, inner ℂ ((show EuclideanSpace ℂ T from v) t) ((show EuclideanSpace ℂ T from w) t)
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

end Kaplansky

end

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
variable {B S T : Type*} [TopologicalSpace B] [Fintype S] [Fintype T]
  {J : S⊕T → Type*} (L : ∀ u, VectorBundleCore ℂ B ℂ (J u))

def lineSumFst (x : B) : (finiteLineSumCore L).Fiber x →ₗ[ℂ]
    (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber x where
  toFun v := WithLp.toLp 2 (fun s => (show EuclideanSpace ℂ (S⊕T) from v) (Sum.inl s))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineSumSnd (x : B) : (finiteLineSumCore L).Fiber x →ₗ[ℂ]
    (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber x where
  toFun v := WithLp.toLp 2 (fun t => (show EuclideanSpace ℂ (S⊕T) from v) (Sum.inr t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_lineSumFst : Continuous (fun z : TotalSpace (EuclideanSpace ℂ (S⊕T))
    (finiteLineSumCore L).Fiber => TotalSpace.mk' (EuclideanSpace ℂ S) z.proj (lineSumFst L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  exact ⟨FiberBundle.continuous_proj _ _,fun s => continuous_finiteLineSumComponent L (Sum.inl s)⟩

theorem continuous_lineSumSnd : Continuous (fun z : TotalSpace (EuclideanSpace ℂ (S⊕T))
    (finiteLineSumCore L).Fiber => TotalSpace.mk' (EuclideanSpace ℂ T) z.proj (lineSumSnd L z.proj z.2)) := by
  apply (continuous_finiteLineSum_iff _ _).mpr
  exact ⟨FiberBundle.continuous_proj _ _,fun t => continuous_finiteLineSumComponent L (Sum.inr t)⟩

theorem lineSumFst_inner (x : B)
    (v : (finiteLineSumCore (fun s => L (Sum.inl s))).Fiber x)
    (w : (finiteLineSumCore L).Fiber x) :
    inner ℂ (lineSumFst L x w) v = inner ℂ w (lineSumInl L x v) := by
  change EuclideanSpace ℂ S at v
  change EuclideanSpace ℂ (S⊕T) at w
  change (∑ s, inner ℂ (w (Sum.inl s)) (v s)) =
    ∑ u : S ⊕ T, inner ℂ (w u) (Sum.elim (fun s => v s) (fun _ => 0) u)
  simp [Fintype.sum_sum_type]

theorem lineSumSnd_inner (x : B)
    (v : (finiteLineSumCore (fun t => L (Sum.inr t))).Fiber x)
    (w : (finiteLineSumCore L).Fiber x) :
    inner ℂ (lineSumSnd L x w) v = inner ℂ w (lineSumInr L x v) := by
  change EuclideanSpace ℂ T at v
  change EuclideanSpace ℂ (S⊕T) at w
  change (∑ t, inner ℂ (w (Sum.inr t)) (v t)) =
    ∑ u : S ⊕ T, inner ℂ (w u) (Sum.elim (fun _ => 0) (fun t => v t) u)
  simp [Fintype.sum_sum_type]

theorem lineSumFst_comp_inl (x : B) : (lineSumFst L x).comp (lineSumInl L x) = LinearMap.id := by
  ext v
  rfl

theorem lineSumSnd_comp_inr (x : B) : (lineSumSnd L x).comp (lineSumInr L x) = LinearMap.id := by
  ext v
  rfl

theorem lineSum_inl_fst_add_inr_snd (x : B) :
    (lineSumInl L x).comp (lineSumFst L x) + (lineSumInr L x).comp (lineSumSnd L x) = LinearMap.id := by
  ext v
  apply (EuclideanSpace.equiv (S⊕T) ℂ).injective
  funext u
  cases u with
  | inl s => exact add_zero ((show EuclideanSpace ℂ (S⊕T) from v) (Sum.inl s))
  | inr t => exact zero_add ((show EuclideanSpace ℂ (S⊕T) from v) (Sum.inr t))

end Kaplansky

end

end OAI
