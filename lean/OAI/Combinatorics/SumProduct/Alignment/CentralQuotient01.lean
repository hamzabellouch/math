import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalQuotient01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open Topology
open scoped Pointwise
namespace CompactGroupProducts
variable {G : Type*} [Group G] [TopologicalSpace G]

 
def HasCompactReps (H Γ : Subgroup G) : Prop :=
  ∃ C : Set G, IsCompact C ∧ C ⊆ H ∧
    ∀ g ∈ H, ∃ c ∈ C, c⁻¹ * g ∈ Γ

variable [IsTopologicalGroup G] [T2Space G]

 
lemma isClosed_subset_lattice (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    {S : Set G} (hS : S ⊆ Γ) : IsClosed S := by
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  have hc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have he : Subtype.val '' (Subtype.val ⁻¹' S : Set Γ) = S := by
    ext x
    exact ⟨fun ⟨y,hy,he⟩ => he ▸ hy,fun hx => ⟨⟨x,hS hx⟩,hx,rfl⟩⟩
  rw [← he]
  exact hc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_discrete _)

 

lemma HasCompactReps.isClosed {H Γ : Subgroup G}
    (h : HasCompactReps H Γ) (hΓ : IsDiscrete (Γ : Set G)) : IsClosed (H : Set G) := by
  obtain ⟨C,hC,hCH,hr⟩ := h
  have hE : IsClosed ((H : Set G) ∩ Γ) := isClosed_subset_lattice Γ hΓ
    (fun _ hx => hx.2)
  have he : (H : Set G) = C * ((H : Set G) ∩ Γ) := by
    ext g
    constructor
    · intro hg
      obtain ⟨c,hc,hcg⟩ := hr g hg
      exact ⟨c,hc,c⁻¹*g,⟨H.mul_mem (H.inv_mem (hCH hc)) hg,hcg⟩,by simp⟩
    · rintro ⟨c,hc,e,he,rfl⟩
      exact H.mul_mem (hCH hc) he.1
  rw [he]
  exact hE.mul_left_of_isCompact hC

 

theorem HasCompactReps.discrete_map {N Γ : Subgroup G} [N.Normal]
    (h : HasCompactReps N Γ) (hΓ : IsDiscrete (Γ : Set G)) :
    DiscreteTopology (Γ.map (QuotientGroup.mk' N)) := by
  obtain ⟨C,hC,hCN,hr⟩ := h
  let F : Set G := (Γ : Set G) \ N
  have hF : IsClosed F := isClosed_subset_lattice Γ hΓ (fun _ hx => hx.1)
  let U : Set G := (F * C⁻¹)ᶜ
  have hU : IsOpen U := (hF.mul_right_of_isCompact hC.inv).isOpen_compl
  have h1U : (1:G) ∈ U := by
    rintro ⟨x,hx,y,hy,he⟩
    have hxN : x ∈ N := by
      have he' : x = y⁻¹ := (mul_eq_one_iff_eq_inv).mp he
      rw [he']
      exact hCN hy
    exact hx.2 hxN
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let L := Γ.map π
  let V : Set (G ⧸ N) := π '' U
  have hV : IsOpen V := QuotientGroup.isOpenMap_coe U hU
  have h1V : (1:G ⧸ N) ∈ V := ⟨1,h1U,map_one π⟩
  have hev : ∀ z ∈ L, z ∈ V → z = 1 := by
    rintro _ ⟨γ,hγ,rfl⟩ ⟨u,hu,heu⟩
    have huγ : u⁻¹*γ ∈ N := QuotientGroup.eq.mp heu
    obtain ⟨c,hc,hcγ⟩ := hr _ huγ
    let e := c⁻¹*(u⁻¹*γ)
    have heΓ : e ∈ Γ := hcγ
    have heN : e ∈ N := N.mul_mem (N.inv_mem (hCN hc)) huγ
    have hγN : γ ∈ N := by
      by_contra hγN
      have hf : γ*e⁻¹ ∈ F := by
        refine ⟨Γ.mul_mem hγ (Γ.inv_mem heΓ),?_⟩
        intro hn
        exact hγN (by simpa [mul_assoc] using N.mul_mem hn heN)
      apply hu
      refine ⟨γ*e⁻¹,hf,c⁻¹,?_,?_⟩
      · simpa only [Set.mem_inv,inv_inv] using hc
      · dsimp [e]
        group
    exact (QuotientGroup.eq_one_iff γ).mpr hγN
  have hpre : Subtype.val ⁻¹' V = ({1} : Set L) := by
    ext z
    constructor
    · intro hz
      exact Subtype.ext (hev z z.property hz)
    · intro hz
      have hz' : z = 1 := hz
      simpa [hz'] using h1V
  apply discreteTopology_iff_isOpen_singleton_one.mpr
  rw [← hpre]
  exact hV.preimage continuous_subtype_val

omit [IsTopologicalGroup G] [T2Space G] in
 

lemma HasCompactReps.quotient_compactSpace {Γ : Subgroup G}
    (h : HasCompactReps ⊤ Γ) : CompactSpace (G ⧸ Γ) := by
  obtain ⟨C,hC,_,hr⟩ := h
  have he : QuotientGroup.mk (s := Γ) '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    induction x using Quotient.inductionOn with | h x =>
      obtain ⟨c,hc,hcx⟩ := hr x (Subgroup.mem_top _)
      exact ⟨c,hc,QuotientGroup.eq.mpr hcx⟩
  exact ⟨he ▸ hC.image QuotientGroup.continuous_mk⟩

omit [IsTopologicalGroup G] [T2Space G] in
 

lemma HasCompactReps.map_surjective {K : Type*} [Group K] [TopologicalSpace K]
    {Γ : Subgroup G} (h : HasCompactReps ⊤ Γ) (φ : G →* K)
    (hc : Continuous φ) (hs : Function.Surjective φ) :
    HasCompactReps ⊤ (Γ.map φ) := by
  obtain ⟨C,hC,_,hr⟩ := h
  refine ⟨φ '' C,hC.image hc,Set.subset_univ _,?_⟩
  intro y _
  obtain ⟨x,rfl⟩ := hs y
  obtain ⟨c,hc,hcx⟩ := hr x (Subgroup.mem_top _)
  exact ⟨φ c,⟨c,hc,rfl⟩,⟨c⁻¹*x,hcx,by simp⟩⟩

 

theorem rational_normal_quotient (N Γ : Subgroup G) [N.Normal]
    (hG : HasCompactReps ⊤ Γ) (hN : HasCompactReps N Γ)
    (hΓ : IsDiscrete (Γ : Set G)) :
    IsClosed (N : Set G) ∧
    DiscreteTopology (Γ.map (QuotientGroup.mk' N)) ∧
    CompactSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)) := by
  refine ⟨hN.isClosed hΓ,hN.discrete_map hΓ,?_⟩
  exact (hG.map_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)).quotient_compactSpace

end CompactGroupProducts

 

open Topology Set
namespace CentralQuotientAction
variable {G : Type*} [Group G] (N Γ : Subgroup G)

lemma central_kernel_normal (hN : N ≤ Subgroup.center G) :
    (Γ.comap N.subtype).Normal := by
  constructor
  intro x hx n
  change (n:G) * (x:G) * (n:G)⁻¹ ∈ Γ
  rw [(Subgroup.mem_center_iff.mp (hN x.property) (n:G)),mul_assoc,mul_inv_cancel,mul_one]
  exact hx

lemma central_action_kernel (hN : N ≤ Subgroup.center G) :
    Γ.comap N.subtype ≤ (MulAction.toPermHom N (G ⧸ Γ)).ker := by
  intro n hn
  apply Equiv.ext
  intro x
  induction x using Quotient.inductionOn with | h g =>
    change QuotientGroup.mk ((n:G)*g) = QuotientGroup.mk g
    rw [← Subgroup.mem_center_iff.mp (hN n.property) g]
    exact QuotientGroup.mk_mul_of_mem _ hn

@[instance_reducible]
noncomputable def action (hN : N ≤ Subgroup.center G)
    [(Γ.comap N.subtype).Normal] : MulAction (N ⧸ Γ.comap N.subtype) (G ⧸ Γ) :=
  MulAction.compHom _ (QuotientGroup.lift _ (MulAction.toPermHom N (G ⧸ Γ))
    (central_action_kernel N Γ hN))

theorem action_mk (hN : N ≤ Subgroup.center G) [(Γ.comap N.subtype).Normal]
    (n : N) (x : G ⧸ Γ) :
    letI := action N Γ hN
    (QuotientGroup.mk n : N ⧸ Γ.comap N.subtype) • x = n • x := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

lemma continuous_action (hN : N ≤ Subgroup.center G) [(Γ.comap N.subtype).Normal] :
    letI := action N Γ hN
    ContinuousSMul (N ⧸ Γ.comap N.subtype) (G ⧸ Γ) := by
  let := action N Γ hN
  constructor
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := Γ.comap N.subtype)).prodMap
    (IsOpenQuotientMap.id (X := G ⧸ Γ))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : N × (G ⧸ Γ) => (z.1:G) • z.2)
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

omit [IsTopologicalGroup G] in
lemma compact_central_quotient (h : CompactGroupProducts.HasCompactReps N Γ) :
    CompactSpace (N ⧸ Γ.comap N.subtype) := by
  obtain ⟨C,hC,hCN,hr⟩ := h
  have hC' : IsCompact (Subtype.val ⁻¹' C : Set N) := by
    apply IsInducing.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' (Subtype.val ⁻¹' C : Set N) = C := by
      ext x
      exact ⟨fun ⟨_,hx,e⟩ => e ▸ hx,fun hx => ⟨⟨x,hCN hx⟩,hx,rfl⟩⟩
    exact he.symm ▸ hC
  apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
  refine ⟨Subtype.val ⁻¹' C,hC',fun _ _ => Subgroup.mem_top _,?_⟩
  intro n _
  obtain ⟨c,hc,hcn⟩ := hr n n.property
  exact ⟨⟨c,hCN hc⟩,hc,hcn⟩

variable [N.Normal]

 

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientMap_fibers (hN : N ≤ Subgroup.center G)
    [(Γ.comap N.subtype).Normal] :
    letI := action N Γ hN
    ∀ x z : G ⧸ Γ,
      RationalQuotientFunctions.quotientMap N Γ x =
        RationalQuotientFunctions.quotientMap N Γ z →
      ∃ k : N ⧸ Γ.comap N.subtype, k • x = z := by
  let := action N Γ hN
  intro x z
  induction x using Quotient.inductionOn with | h g =>
    induction z using Quotient.inductionOn with | h h =>
      intro he
      have hh : (QuotientGroup.mk' N g)⁻¹ * QuotientGroup.mk' N h ∈
          Γ.map (QuotientGroup.mk' N) := QuotientGroup.eq.mp he
      obtain ⟨γ,hγ,heγ⟩ := hh
      let n := g⁻¹*h*γ⁻¹
      have hn : n ∈ N := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' N (g⁻¹*h*γ⁻¹) = 1
        simp only [map_mul,map_inv]
        rw [← heγ,mul_inv_cancel]
      refine ⟨QuotientGroup.mk (⟨n,hn⟩ : N),?_⟩
      change QuotientGroup.mk (n*g) = QuotientGroup.mk h
      rw [← Subgroup.mem_center_iff.mp (hN hn) g]
      have heq : g*n = h*γ⁻¹ := by dsimp [n]; group
      rw [heq]
      exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem hγ)

open MeasureTheory

 

omit [TopologicalSpace G] [IsTopologicalGroup G] [N.Normal] in
lemma invariant_central_action (hN : N ≤ Subgroup.center G)
    [(Γ.comap N.subtype).Normal] [MeasurableSpace (G ⧸ Γ)]
    (μ : Measure (G ⧸ Γ)) [SMulInvariantMeasure G (G ⧸ Γ) μ] :
    letI := action N Γ hN
    SMulInvariantMeasure (N ⧸ Γ.comap N.subtype) (G ⧸ Γ) μ := by
  let := action N Γ hN
  constructor
  intro k s hs
  induction k using Quotient.inductionOn with | h n =>
    exact SMulInvariantMeasure.measure_preimage_smul (μ := μ) (n:G) hs

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma quotientMap_smul (g : G) (x : G ⧸ Γ) :
    RationalQuotientFunctions.quotientMap N Γ (g • x) =
      (QuotientGroup.mk' N g) • RationalQuotientFunctions.quotientMap N Γ x := by
  induction x using Quotient.inductionOn with | h a =>
    change QuotientGroup.mk (QuotientGroup.mk' N (g*a)) =
      QuotientGroup.mk (QuotientGroup.mk' N g * QuotientGroup.mk' N a)
    rw [map_mul]

lemma invariant_quotientMap [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    [MeasurableSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))]
    [BorelSpace ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))]
    (μ : Measure (G ⧸ Γ)) [SMulInvariantMeasure G (G ⧸ Γ) μ] :
    SMulInvariantMeasure (G ⧸ N) ((G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N))
      (Measure.map (RationalQuotientFunctions.quotientMap N Γ) μ) := by
  constructor
  intro g s hs
  induction g using Quotient.inductionOn with | h g =>
    have hp := (RationalQuotientFunctions.continuous_quotientMap N Γ).measurable
    rw [Measure.map_apply hp (hs.preimage (measurable_const_smul _)),Measure.map_apply hp hs]
    have he : RationalQuotientFunctions.quotientMap N Γ ⁻¹' ((QuotientGroup.mk' N g • ·) ⁻¹' s) =
        (g • ·) ⁻¹' (RationalQuotientFunctions.quotientMap N Γ ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage,quotientMap_smul]
    change μ (RationalQuotientFunctions.quotientMap N Γ ⁻¹'
      ((QuotientGroup.mk' N g • ·) ⁻¹' s)) = _
    rw [he]
    exact SMulInvariantMeasure.measure_preimage_smul (μ := μ) g (hs.preimage hp)

end CentralQuotientAction

 

end
end
end
end

end OAI
