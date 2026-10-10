import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.LocalProjectiveTopology
import OAI.Probability.CriticalPercolation.ProductMeasure.CompactInvariantMeasure

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory Module Metric TopologicalSpace
open scoped Classical Topology

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

def nzImage (a : V ≃L[K] V) (v : NZ V) : NZ V :=
  ⟨a v,fun he => v.property (a.injective (he.trans a.map_zero.symm))⟩

def action (a : V ≃L[K] V) : Space K V → Space K V :=
  Quotient.map (nzImage a) (by
    intro v w h
    obtain ⟨c,hc⟩ := h
    refine ⟨c,Subtype.ext ?_⟩
    change (c:K) • a (w:V)=a (v:V)
    rw [←map_smul]
    exact congrArg a (congrArg Subtype.val hc))

@[simp] lemma action_point (a : V ≃L[K] V) (v : NZ V) :
    action a (point K V v)=point K V (nzImage a v) := rfl

@[simp] lemma action_one (q : Space K V) : action (1:V ≃L[K] V) q=q := by
  obtain ⟨v,rfl⟩ := point_surjective K V q
  rfl

lemma action_mul (a b : V ≃L[K] V) (q : Space K V) :
    action (a*b) q=action a (action b q) := by
  obtain ⟨v,rfl⟩ := point_surjective K V q
  rfl

lemma continuous_action (a : V ≃L[K] V) : Continuous (action a) := by
  apply (openQuotient_point K V).isQuotientMap.continuous_iff.mpr
  exact (continuous_point K V).comp ((a.continuous.comp continuous_subtype_val).subtype_mk _)

variable {G : Type*} [Group G]
@[instance_reducible]
def mulAction (ρ : G →* (V ≃L[K] V)) : MulAction G (Space K V) where
  smul g q := action (ρ g) q
  one_smul q := by change action (ρ 1) q=q; rw [map_one,action_one]
  mul_smul g h q := by change action (ρ (g*h)) q=action (ρ g) (action (ρ h) q); rw [map_mul,action_mul]

lemma continuousConstSMul (ρ : G →* (V ≃L[K] V)) :
    letI := mulAction ρ; ContinuousConstSMul G (Space K V) := by
  let := mulAction ρ
  exact ⟨fun g => continuous_action (ρ g)⟩

instance spaceMeasurable : MeasurableSpace (Space K V) := borel _
instance spaceBorel : BorelSpace (Space K V) := ⟨rfl⟩

lemma exists_invariant_measure [ProperSpace K] [FiniteDimensional K V] [Nontrivial V]
    [DecidableEq G] (ρ : G →* (V ≃L[K] V)) (S : Finset G)
    (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : SparseGrowth.HasDegree S d) :
    ∃ μ : Measure (Space K V), IsProbabilityMeasure μ ∧
      ∀ g, Measure.map (action (ρ g)) μ=μ := by
  let : MetricSpace (Space K V) := metrizableSpaceMetric _
  let := mulAction ρ
  let := continuousConstSMul ρ
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  obtain ⟨μ,hμ⟩ := SparseGrowth.exists_invariant_probability_measure S h1 hgen d hg (point K V ⟨v,hv⟩)
  exact ⟨μ,inferInstance,hμ⟩

def subspace (W : Submodule K V) : Set (Space K V) :=
  point K V '' {v : NZ V | (v:V)∈W}

lemma point_mem_subspace (W : Submodule K V) (v : NZ V) :
    point K V v∈subspace W ↔ (v:V)∈W := by
  constructor
  · rintro ⟨w,hw,he⟩
    obtain ⟨a,ha⟩ := (point_eq_iff v w).mp he.symm
    exact ha ▸ W.smul_mem a hw
  · intro hv
    exact ⟨v,hv,rfl⟩

lemma preimage_point_subspace (W : Submodule K V) :
    point K V ⁻¹' subspace W={v : NZ V | (v:V)∈W} := by
  ext v
  exact point_mem_subspace W v

lemma closed_subspace [CompleteSpace K] [FiniteDimensional K V] (W : Submodule K V) :
    IsClosed (subspace W) := by
  apply (openQuotient_point K V).isQuotientMap.isClosed_preimage.mp
  rw [preimage_point_subspace]
  exact W.closed_of_finiteDimensional.preimage continuous_subtype_val

lemma measurable_subspace [CompleteSpace K] [FiniteDimensional K V] (W : Submodule K V) :
    MeasurableSet (subspace W) := (closed_subspace W).measurableSet

@[simp] lemma subspace_inf (U W : Submodule K V) :
    subspace (U⊓W)=subspace U∩subspace W := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [mem_inter_iff,point_mem_subspace,Submodule.mem_inf]

@[simp] lemma subspace_bot : subspace (⊥:Submodule K V)=∅ := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [point_mem_subspace,Submodule.mem_bot,mem_empty_iff_false,iff_false]
  exact v.property

@[simp] lemma subspace_top : subspace (⊤:Submodule K V)=univ := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [point_mem_subspace,Submodule.mem_top,mem_univ]

lemma preimage_action_subspace (a : V ≃L[K] V) (W : Submodule K V) :
    action a ⁻¹' subspace (W.map a.toLinearEquiv.toLinearMap)=subspace W := by
  ext q
  obtain ⟨v,rfl⟩ := point_surjective K V q
  simp only [mem_preimage,action_point,point_mem_subspace]
  change a (v:V)∈W.map a.toLinearEquiv.toLinearMap ↔ (v:V)∈W
  constructor
  · rintro ⟨w,hw,he⟩
    exact a.injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

end CriticalPercolation.LocalProjective
end
end

end OAI
