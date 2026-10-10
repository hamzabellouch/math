import OAI.Analysis.StrictMeans.DescendingRanks

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma measurableSet_exists_closed_open {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X] [PerfectlyNormalSpace (P × X)]
    {C U : Set (P × X)} (hC : IsClosed C) (hU : IsOpen U) :
    MeasurableSet {p : P | ∃ x : X, (p,x) ∈ C ∩ U} := by
  obtain ⟨W,hW,hUW⟩ := hU.isClosed_compl.isGδ.eq_iInter_nat
  have he : U = ⋃ n : ℕ, (W n)ᶜ := by
    rw [← compl_iInter, ← hUW, compl_compl]
  have hp : {p : P | ∃ x : X, (p,x) ∈ C ∩ U} =
      ⋃ n : ℕ, {p : P | ∃ x : X, (p,x) ∈ C ∩ (W n)ᶜ} := by
    ext p
    simp only [mem_ofPred_eq,mem_iUnion,mem_inter_iff,he]
    constructor
    · rintro ⟨x,hx,n,hn⟩
      exact ⟨n,x,hx,hn⟩
    · rintro ⟨n,x,hx,hn⟩
      exact ⟨x,hx,n,hn⟩
  rw [hp]
  exact MeasurableSet.iUnion (fun n =>
    measurableSet_exists_of_closed_sigmaCompact (hC.inter (hW n).isClosed_compl))

lemma finite_ncard_ge_iff_tuple {X : Type*} {S : Set X} (hS : S.Finite) (n : ℕ) :
    n ≤ S.ncard ↔ ∃ t : Fin n → X, Function.Injective t ∧ ∀ i, t i ∈ S := by
  classical
  let := hS.fintype
  have hc : S.ncard = Fintype.card S := by
    rw [Set.ncard_eq_toFinset_card']
    exact Set.toFinset_card S
  rw [hc]
  constructor
  · intro hn
    let e : Fin n ↪ S := (Fin.castLEEmb hn).trans (Fintype.equivFin S).symm.toEmbedding
    exact ⟨fun i => (e i : X), Subtype.val_injective.comp e.injective, fun i => (e i).2⟩
  · rintro ⟨t,ht,hS⟩
    simpa using Fintype.card_le_of_injective (fun i : Fin n => (⟨t i,hS i⟩ : S))
      (fun i j h => ht (congrArg Subtype.val h))

lemma measurable_ncard_locally_closed_fiber {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [TopologicalSpace.MetrizableSpace P]
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SigmaCompactSpace X]
    {C U : Set (P × X)} (hC : IsClosed C) (hU : IsOpen U)
    (hf : ∀ p : P, {x : X | (p,x) ∈ C ∩ U}.Finite) :
    Measurable (fun p : P => {x : X | (p,x) ∈ C ∩ U}.ncard) := by
  apply measurable_of_Ici
  intro n
  let Cn : Set (P × (Fin n → X)) := {q | ∀ i, (q.1,q.2 i) ∈ C}
  let Un : Set (P × (Fin n → X)) :=
    {q | (∀ i, (q.1,q.2 i) ∈ U) ∧ Function.Injective q.2}
  have hCn : IsClosed Cn := by
    change IsClosed {q : P × (Fin n → X) | ∀ i, (q.1,q.2 i) ∈ C}
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => hC.preimage
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
  have hUn : IsOpen Un := by
    have hmem : IsOpen {q : P × (Fin n → X) | ∀ i, (q.1,q.2 i) ∈ U} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => hU.preimage
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
    have hinj : IsOpen {q : P × (Fin n → X) | Function.Injective q.2} := by
      have he : {q : P × (Fin n → X) | Function.Injective q.2} =
          {q | ∀ i j : Fin n, i ≠ j → q.2 i ≠ q.2 j} := by
        ext q
        simp only [mem_ofPred_eq]
        constructor
        · intro h i j hij heq
          exact hij (h heq)
        · intro h i j heq
          by_contra hij
          exact h i j hij heq
      rw [he]
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
        isOpen_iInter_of_finite (fun _ => isOpen_ne_fun
          ((continuous_apply i).comp continuous_snd) ((continuous_apply j).comp continuous_snd))))
    exact hmem.inter hinj
  have hp := measurableSet_exists_closed_open hCn hUn
  convert hp using 1
  ext p
  simp only [mem_preimage,mem_Ici,mem_ofPred_eq,Cn,Un,mem_inter_iff]
  have htest := finite_ncard_ge_iff_tuple (hf p) n
  simp only [mem_inter_iff] at htest
  rw [htest]
  constructor
  · rintro ⟨t,ht,hm⟩
    exact ⟨t,fun i => (hm i).1,fun i => (hm i).2,ht⟩
  · rintro ⟨t,hC,hU,ht⟩
    exact ⟨t,ht,fun i => ⟨hC i,hU i⟩⟩

lemma measurable_of_borel_graph {P X : Type*}
    [MeasurableSpace P] [MeasurableSpace X]
    [StandardBorelSpace P] [StandardBorelSpace X]
    {f : P → X} (hg : MeasurableSet {q : P × X | f q.1 = q.2}) :
    Measurable f := by
  let R : Set (P × X) := {q | f q.1 = q.2}
  have : StandardBorelSpace R := hg.standardBorel
  let π : R → P := fun q => q.1.1
  have hπ : MeasurableEmbedding π :=
    (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (by
      intro q r he
      apply Subtype.ext
      apply Prod.ext he
      exact q.2.symm.trans ((congrArg f he).trans r.2))
  intro A hA
  have hm : MeasurableSet {q : R | q.1.2 ∈ A} :=
    (measurable_snd.comp measurable_subtype_coe) hA
  have hi := hπ.measurableSet_image.mpr hm
  convert hi using 1
  ext p
  simp only [mem_preimage,mem_image,mem_ofPred_eq,π]
  constructor
  · intro hp
    exact ⟨⟨(p,f p),rfl⟩,hp,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    rwa [q.2]

end
end StrictInverseFirstPower

end

end OAI
