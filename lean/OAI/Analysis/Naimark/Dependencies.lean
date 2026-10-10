import OAI.Analysis.Naimark.CAR

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
variable {A ι : Type*} [CStarAlgebra A]

def generatedFamily (base : Set A) (v : ι → A) (S : Set ι) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ (base ∪ v '' S)).topologicalClosure

theorem generatedFamily_mono (base : Set A) (v : ι → A) :
    Monotone (generatedFamily base v) := by
  intro S T h
  exact StarSubalgebra.topologicalClosure_mono
    (StarAlgebra.adjoin_mono (Set.union_subset_union_right base (Set.image_mono h)))

theorem countable_submonoidClosure (s : Set A) (hs : s.Countable) :
    (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  rw [Submonoid.closure_eq_mrange,MonoidHom.coe_mrange]
  exact Set.countable_range _

theorem separable_submonoidClosure (s : Set A) (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (Submonoid.closure s : Set A) := by
  obtain ⟨d,hd,hsd⟩ := hs
  have hm : Submonoid.closure s ≤ (Submonoid.closure d).topologicalClosure := by
    apply Submonoid.closure_le.mpr
    exact hsd.trans (closure_mono (Submonoid.subset_closure))
  exact ((countable_submonoidClosure d hd).isSeparable.closure).mono hm

theorem separable_starAdjoin (s : Set A) (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have hstar : TopologicalSpace.IsSeparable (star s) := by
    simpa only [Set.image_star] using hs.image continuous_star
  have h := (separable_submonoidClosure (s ∪ star s) (hs.union hstar)).span (R := ℂ)
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rwa [StarAlgebra.adjoin_eq_span]

theorem generatedFamily_separable (base : Set A) (v : ι → A)
    (hbase : TopologicalSpace.IsSeparable base) {S : Set ι} (hS : S.Countable) :
    TopologicalSpace.IsSeparable (generatedFamily base v S : Set A) :=
  (separable_starAdjoin _ (hbase.union (hS.image v).isSeparable)).closure

theorem generatedFamily_isClosed (base : Set A) (v : ι → A) (S : Set ι) :
    IsClosed (generatedFamily base v S : Set A) := isClosed_closure

theorem generatedFamily_contains_base (base : Set A) (v : ι → A) (S : Set ι) :
    base ⊆ generatedFamily base v S :=
  fun _ h => subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inl h))

theorem generatedFamily_contains (base : Set A) (v : ι → A) {S : Set ι} {j : ι}
    (hj : j ∈ S) : v j ∈ generatedFamily base v S :=
  subset_closure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨j,hj,rfl⟩))

theorem starAdjoin_countable_support (base : Set A) (v : ι → A) (T : Set ι)
    {a : A} (ha : a ∈ StarAlgebra.adjoin ℂ (base ∪ v '' T)) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ T ∧ a ∈ generatedFamily base v S := by
  induction ha using StarAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨j,hj,rfl⟩
    · exact ⟨∅,Set.countable_empty,Set.empty_subset _,generatedFamily_contains_base base v ∅ hx⟩
    · exact ⟨{j},Set.countable_singleton _,Set.singleton_subset_iff.mpr hj,
        generatedFamily_contains base v (Set.mem_singleton j)⟩
  | algebraMap r =>
    exact ⟨∅,Set.countable_empty,Set.empty_subset _,(generatedFamily base v ∅).algebraMap_mem r⟩
  | add x y hx hy ix iy =>
    obtain ⟨S,hSc,hST,hS⟩ := ix
    obtain ⟨R,hRc,hRT,hR⟩ := iy
    exact ⟨S ∪ R,hSc.union hRc,Set.union_subset hST hRT,
      (generatedFamily base v (S ∪ R)).add_mem
        (generatedFamily_mono base v Set.subset_union_left hS)
        (generatedFamily_mono base v Set.subset_union_right hR)⟩
  | mul x y hx hy ix iy =>
    obtain ⟨S,hSc,hST,hS⟩ := ix
    obtain ⟨R,hRc,hRT,hR⟩ := iy
    exact ⟨S ∪ R,hSc.union hRc,Set.union_subset hST hRT,
      (generatedFamily base v (S ∪ R)).mul_mem
        (generatedFamily_mono base v Set.subset_union_left hS)
        (generatedFamily_mono base v Set.subset_union_right hR)⟩
  | star x hx ix =>
    obtain ⟨S,hSc,hST,hS⟩ := ix
    exact ⟨S,hSc,hST,star_mem hS⟩

theorem generatedFamily_countable_support (base : Set A) (v : ι → A) (T : Set ι)
    {a : A} (ha : a ∈ generatedFamily base v T) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ T ∧ a ∈ generatedFamily base v S := by
  obtain ⟨u,hu,hlim⟩ := mem_closure_iff_seq_limit.mp ha
  choose S hSc hST hS using fun n => starAdjoin_countable_support base v T (hu n)
  refine ⟨⋃ n, S n,Set.countable_iUnion hSc,Set.iUnion_subset hST,?_⟩
  apply (generatedFamily_isClosed base v (⋃ n, S n)).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    generatedFamily_mono base v (Set.subset_iUnion S n) (hS n)

theorem generatedFamily_iUnion (base : Set A) (v : ι → A) (N : ℕ → Set ι)
    (hN : Monotone N) :
    (generatedFamily base v (⋃ n, N n) : Set A) ⊆
      closure (⋃ n, (generatedFamily base v (N n) : Set A)) := by
  let C : StarSubalgebra ℂ A := (⨆ n, generatedFamily base v (N n)).topologicalClosure
  have hd : Directed (· ≤ ·) (fun n => generatedFamily base v (N n)) :=
    ((generatedFamily_mono base v).comp hN).directed_le
  have hcoe : (C : Set A) = closure (⋃ n, (generatedFamily base v (N n) : Set A)) := by
    change closure (((⨆ n, generatedFamily base v (N n)) : StarSubalgebra ℂ A) : Set A) = _
    rw [StarSubalgebra.coe_iSup_of_directed hd]
  rw [← hcoe]
  change generatedFamily base v (⋃ n, N n) ≤ C
  apply StarSubalgebra.topologicalClosure_minimal _ (show IsClosed (C : Set A) from isClosed_closure)
  apply StarAlgebra.adjoin_le
  intro x hx
  rcases hx with hx | ⟨j,hj,rfl⟩
  · exact subset_closure ((le_iSup (fun n => generatedFamily base v (N n)) 0)
      (generatedFamily_contains_base base v (N 0) hx))
  · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hj
    exact subset_closure ((le_iSup (fun n => generatedFamily base v (N n)) n)
      (generatedFamily_contains base v hn))

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_state_excision_witness (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : A, 0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧ ‖x*(a-f a • (1:A))*x‖ < ε := by
  let F := positiveOfSquares f hf.1.2
  let π := F.gnsNonUnitalStarAlgHom
  let ξ := gnsVector F
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1
  have hexc := (pureExcisionNet_excision π hπ ξ hξ a).norm
  have hcoeff : ⟪ξ,π a ξ⟫_ℂ = f a := gnsVector_coefficient F a
  simp only [hcoeff,norm_zero] at hexc
  obtain ⟨i,hi⟩ := (hexc.eventually (gt_mem_nhds hε)).exists
  refine ⟨pureExcisionNet π ξ i,pureExcisionNet_nonneg π ξ i,
    pureExcisionNet_norm π ξ i,?_,hi⟩
  change F (pureExcisionNet π ξ i) = 1
  rw [← gnsVector_coefficient F]
  change ⟪ξ,π (pureExcisionNet π ξ i) ξ⟫_ℂ = 1
  rw [pureExcisionNet_fixes π (by change F.gnsStarAlgHom 1 = 1; exact map_one _) ξ i]
  rw [inner_self_eq_norm_sq_to_K, hξ]
  norm_num

end

section
variable {ι : Type*}

def DependencyClosed (I : ι → Set ι) (S : Set ι) : Prop := ∀ j ∈ S, I j ⊆ S

def dependencyStep (I : ι → Set ι) (S : Set ι) : Set ι := S ∪ ⋃ j ∈ S, I j

def dependencyClosure (I : ι → Set ι) (S : Set ι) : Set ι :=
  ⋃ n : ℕ, (dependencyStep I)^[n] S

theorem subset_dependencyStep (I : ι → Set ι) (S : Set ι) : S ⊆ dependencyStep I S :=
  Set.subset_union_left

theorem subset_dependencyClosure (I : ι → Set ι) (S : Set ι) : S ⊆ dependencyClosure I S := by
  intro j hj
  exact Set.mem_iUnion.mpr ⟨0,hj⟩

theorem dependencyClosure_closed (I : ι → Set ι) (S : Set ι) :
    DependencyClosed I (dependencyClosure I S) := by
  intro j hj k hk
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hj
  apply Set.mem_iUnion.mpr
  refine ⟨n+1,?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hn,hk⟩⟩)

theorem dependencyStep_countable (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    {S : Set ι} (hS : S.Countable) : (dependencyStep I S).Countable :=
  hS.union (hS.biUnion (fun j _ => hI j))

theorem dependencyClosure_countable (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    {S : Set ι} (hS : S.Countable) : (dependencyClosure I S).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dependencyStep_countable I hI ih

theorem exists_countable_dependencyClosure (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    {S : Set ι} (hS : S.Countable) :
    ∃ T : Set ι, T.Countable ∧ S ⊆ T ∧ DependencyClosed I T :=
  ⟨dependencyClosure I S,dependencyClosure_countable I hI hS,
    subset_dependencyClosure I S,dependencyClosure_closed I S⟩

theorem DependencyClosed.iUnion {I : ι → Set ι} {κ : Type*} {S : κ → Set ι}
    (h : ∀ k, DependencyClosed I (S k)) : DependencyClosed I (⋃ k, S k) := by
  intro j hj l hl
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hj
  exact Set.mem_iUnion.mpr ⟨k,h k j hk hl⟩

end

open Topology
section
variable {ι X : Type*} [PseudoMetricSpace X]

theorem countable_witness_closure
    (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    (B : Set ι → Set X) (hmono : Monotone B)
    (hsep : ∀ S, S.Countable → TopologicalSpace.IsSeparable (B S))
    (hsupp : ∀ x, ∃ S, S.Countable ∧ x ∈ B S)
    (hlim : ∀ N : ℕ → Set ι, Monotone N →
      B (⋃ n, N n) ⊆ closure (⋃ n, B (N n)))
    (w : X → ℕ → X) :
    ∃ S : Set ι, S.Countable ∧ DependencyClosed I S ∧
      ∃ D : Set X, D.Countable ∧ D ⊆ B S ∧ B S ⊆ closure D ∧
        ∀ a ∈ D, ∀ m, w a m ∈ B S := by
  classical
  choose supp hsuppc hsuppmem using hsupp
  have hex D (hD : D.Countable) := (hsep D hD).exists_countable_dense_subset
  choose d hdsub hdc hddense using hex
  let C := {S : Set ι // S.Countable ∧ DependencyClosed I S}
  let add (S : C) : Set ι := S.1 ∪ ⋃ a ∈ d S.1 S.2.1, ⋃ m : ℕ, supp (w a m)
  have hadd (S : C) : (add S).Countable :=
    S.2.1.union ((hdc S.1 S.2.1).biUnion (fun a _ => Set.countable_iUnion (fun m => hsuppc (w a m))))
  let step (S : C) : C := ⟨dependencyClosure I (add S),
    dependencyClosure_countable I hI (hadd S),dependencyClosure_closed I (add S)⟩
  have hstep (S : C) : S.1 ⊆ (step S).1 :=
    Set.subset_union_left.trans (subset_dependencyClosure I (add S))
  let N : ℕ → C := fun n => step^[n] ⟨∅,Set.countable_empty,by intro j hj; exact hj.elim⟩
  have hNsucc (n : ℕ) : N (n+1) = step (N n) := by
    exact Function.iterate_succ_apply' step n _
  have hNmono : Monotone (fun n => (N n).1) := monotone_nat_of_le_succ (fun n => by
    rw [hNsucc]; exact hstep (N n))
  let S : Set ι := ⋃ n, (N n).1
  let D : Set X := ⋃ n, d (N n).1 (N n).2.1
  have hNS (n : ℕ) : (N n).1 ⊆ S := by
    intro j hj
    exact Set.mem_iUnion.mpr ⟨n,hj⟩
  refine ⟨S,Set.countable_iUnion (fun n => (N n).2.1),
    DependencyClosed.iUnion (fun n => (N n).2.2),D,
    Set.countable_iUnion (fun n => hdc (N n).1 (N n).2.1),?_,?_,?_⟩
  · intro a ha
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    exact hmono (hNS n) (hdsub (N n).1 (N n).2.1 hn)
  · apply (hlim _ hNmono).trans
    apply closure_minimal _ isClosed_closure
    intro a ha
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    exact closure_mono (Set.subset_iUnion _ n) (hddense (N n).1 (N n).2.1 hn)
  · intro a ha m
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    apply hmono (hNS (n+1))
    rw [hNsucc]
    apply hmono (subset_dependencyClosure I (add (N n)))
    apply hmono (show supp (w a m) ⊆ add (N n) from ?_)
    · exact hsuppmem (w a m)
    · intro j hj
      exact Or.inr (Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨hn,
        Set.mem_iUnion.mpr ⟨m,hj⟩⟩⟩)

end

open Topology
open scoped CStarAlgebra ComplexOrder
section
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_restrict_of_witnesses (f : A →L[ℂ] ℂ) (hf : IsState f)
    (C : StarSubalgebra ℂ A) [IsClosed (C : Set A)]
    [PartialOrder C] [StarOrderedRing C]
    (D : Set A) (hD : D ⊆ C) (hd : (C : Set A) ⊆ closure D)
    (hexc : ∀ a ∈ D, ∀ ε : ℝ, 0 < ε → ∃ x ∈ C,
      0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧ ‖x*(a-f a • (1:A))*x‖ < ε) :
    IsPureState (restrictState C.subtype f) := by
  let D' : Set C := Subtype.val ⁻¹' D
  have hd' : Dense D' := by
    apply (IsInducing.subtypeVal.dense_iff).mpr
    intro a
    apply closure_mono (s := D) _ (hd a.property)
    intro z hz
    exact ⟨⟨z,hD hz⟩,hz,rfl⟩
  apply pure_of_dense_excision _ (isState_restrict C.subtype f hf) D' hd'
  intro a ha ε hε
  obtain ⟨x,hx,hxp,hxn,hxf,herr⟩ := hexc a ha ε hε
  refine ⟨⟨x,hx⟩,?_,hxn,hxf,herr⟩
  exact (faithfulStarHom_nonneg_iff C.subtype Subtype.val_injective ⟨x,hx⟩).mp hxp

theorem countable_pure_restriction
    (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    (B : Set ι → StarSubalgebra ℂ A) (hclosed : ∀ S, IsClosed (B S : Set A))
    (hmono : Monotone B)
    (hsep : ∀ S, S.Countable → TopologicalSpace.IsSeparable (B S : Set A))
    (hsupp : ∀ a : A, ∃ S, S.Countable ∧ a ∈ B S)
    (hlim : ∀ N : ℕ → Set ι, Monotone N →
      (B (⋃ n, N n) : Set A) ⊆ closure (⋃ n, (B (N n) : Set A)))
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set ι, S.Countable ∧ DependencyClosed I S ∧
      IsPureState (restrictState (B S).subtype f) := by
  classical
  have hw (a : A) (m : ℕ) := pure_state_excision_witness f hf a
    (1/((m:ℝ)+1)) (by positivity)
  choose w hwp hwn hwf hwe using hw
  obtain ⟨S,hSc,hSI,D,_,hD,hd,hwmem⟩ := countable_witness_closure I hI
    (fun S => (B S : Set A)) (fun _ _ h => hmono h) hsep hsupp hlim w
  refine ⟨S,hSc,hSI,?_⟩
  let : IsClosed (B S : Set A) := hclosed S
  let : PartialOrder (B S) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (B S) := CStarAlgebra.spectralOrderedRing _
  apply pure_restrict_of_witnesses f hf.1 (B S) D hD hd
  intro a ha ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  exact ⟨w a m,hwmem a ha m,hwp a m,hwn a m,hwf a m,(hwe a m).trans hm⟩

end

section
attribute [local instance] generatedFamily_isClosed
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem generatedFamily_countable_pure_restriction
    (base : Set A) (v : ι → A) (hbase : TopologicalSpace.IsSeparable base)
    (hgen : generatedFamily base v Set.univ = ⊤)
    (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set ι, S.Countable ∧ DependencyClosed I S ∧
      IsPureState (restrictState (generatedFamily base v S).subtype f) := by
  apply countable_pure_restriction I hI (generatedFamily base v)
    (generatedFamily_isClosed base v) (generatedFamily_mono base v)
    (fun _ hS => generatedFamily_separable base v hbase hS) ?_
    (generatedFamily_iUnion base v) f hf
  intro a
  have ha : a ∈ generatedFamily base v Set.univ := by rw [hgen]; trivial
  obtain ⟨S,hS,_,haS⟩ := generatedFamily_countable_support base v Set.univ ha
  exact ⟨S,hS,haS⟩

end

section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem StateExtensionUnique.of_comp {φ : A →⋆ₐ[ℂ] B} {ψ : B →⋆ₐ[ℂ] C}
    (hψ : Function.Injective ψ) {f : A →L[ℂ] ℂ}
    (hu : StateExtensionUnique (ψ.comp φ) f) : StateExtensionUnique φ f := by
  intro F G hF hG hrF hrG
  obtain ⟨F',hF',hrF'⟩ := exists_state_extension_of_injective ψ hψ F hF
  obtain ⟨G',hG',hrG'⟩ := exists_state_extension_of_injective ψ hψ G hG
  have hRF : restrictState (ψ.comp φ) F' = f := by
    rw [← restrictState_comp,hrF',hrF]
  have hRG : restrictState (ψ.comp φ) G' = f := by
    rw [← restrictState_comp,hrG',hrG]
  have he := hu F' G' hF' hG' hRF hRG
  rw [← hrF',← hrG',he]

theorem PureUEP.of_comp {φ : A →⋆ₐ[ℂ] B} {ψ : B →⋆ₐ[ℂ] C}
    (hψ : Function.Injective ψ) (hu : PureUEP (ψ.comp φ)) : PureUEP φ :=
  fun f hf => (hu f hf).of_comp hψ

variable [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B]

theorem pure_restrict_of_unique_factor
    (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (hψ : Function.Injective ψ)
    (H : C →L[ℂ] ℂ) (hH : IsState H)
    (hp : IsPureState (restrictState (ψ.comp φ) H))
    (hu : StateExtensionUnique (ψ.comp φ) (restrictState (ψ.comp φ) H)) :
    IsPureState (restrictState ψ H) := by
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  have hb : IsState (restrictState ψ H) := isState_restrict ψ H hH
  have hr : restrictState φ (restrictState ψ H) = restrictState (ψ.comp φ) H :=
    restrictState_comp φ ψ H
  exact unique_lift_pure φ _ hp _ hb hr (fun g hg hgr =>
    hu.of_comp hψ g (restrictState ψ H) hg hb hgr hr)

end

section
variable {A : Type*} [CStarAlgebra A]

theorem pure_restrict_intermediate_subalgebra
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (hST : S ≤ T) (f : A →L[ℂ] ℂ) (hf : IsState f)
    (hp : IsPureState (restrictState S.subtype f))
    (hu : StateExtensionUnique S.subtype (restrictState S.subtype f)) :
    IsPureState (restrictState T.subtype f) := by
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let : PartialOrder T := CStarAlgebra.spectralOrder T
  let : StarOrderedRing T := CStarAlgebra.spectralOrderedRing T
  let φ := StarSubalgebra.inclusion hST
  have he : T.subtype.comp φ = S.subtype := by ext a; rfl
  have hpi : IsPureState (restrictState (T.subtype.comp φ) f) := by rw [he]; exact hp
  have hui : StateExtensionUnique (T.subtype.comp φ)
      (restrictState (T.subtype.comp φ) f) := by rw [he]; exact hu
  exact pure_restrict_of_unique_factor φ T.subtype Subtype.val_injective f hf hpi hui

end

section

universe u
open Set Cardinal Ordinal

theorem countable_bounded_regular (c : Cardinal.{u}) (hc : c.IsRegular)
    (huc : ℵ₀ < c) (S : Set c.ord.ToType) (hS : S.Countable) :
    ∃ β : c.ord.ToType, ∀ x ∈ S, x < β := by
  let b : Ordinal.{u} := ⨆ x : S, (x.val : Ordinal) + 1
  have hb : b < c.ord := by
    apply Ordinal.iSup_add_one_lt_of_lt_cof
    · rw [hc.cof_ord]
      exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt huc
    · intro x
      exact x.val.toOrd.property
  refine ⟨Ordinal.ToType.mk ⟨b,hb⟩,?_⟩
  intro x hx
  apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
  change x.toOrd.val < (Ordinal.ToType.mk ⟨b,hb⟩).toOrd.val
  simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using
    (Ordinal.lt_iSup_add_one (fun y : S => (y.val : Ordinal)) ⟨x,hx⟩)

abbrev constructionCardinal : Cardinal.{u} := Order.succ 𝔠

theorem constructionCardinal_regular : constructionCardinal.{u}.IsRegular :=
  Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

theorem countable_bounded_construction (S : Set constructionCardinal.{u}.ord.ToType)
    (hS : S.Countable) : ∃ β : constructionCardinal.{u}.ord.ToType,
      ∀ x ∈ S, x < β :=
  countable_bounded_regular constructionCardinal constructionCardinal_regular
    (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ 𝔠)) S hS

theorem construction_initial_cardinal_le (β : constructionCardinal.{u}.ord.ToType) :
    (β : Ordinal).card ≤ 𝔠 := by
  have h : (β : Ordinal).card < constructionCardinal :=
    Cardinal.lt_ord.mp (show (β : Ordinal) < constructionCardinal.ord from β.toOrd.property)
  exact (Order.lt_succ_iff).mp h

end

section
attribute [local instance] generatedFamily_isClosed
universe u v
variable {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem bounded_pure_determination
    (base : Set A) (v : constructionCardinal.{u}.ord.ToType → A)
    (S : Set constructionCardinal.{u}.ord.ToType) (hS : S.Countable)
    (f : A →L[ℂ] ℂ) (hf : IsState f)
    (hp : IsPureState (restrictState (generatedFamily base v S).subtype f))
    (hu : StateExtensionUnique (generatedFamily base v S).subtype
      (restrictState (generatedFamily base v S).subtype f)) :
    ∃ β : constructionCardinal.{u}.ord.ToType,
      IsPureState (restrictState (generatedFamily base v (Set.Iio β)).subtype f) := by
  obtain ⟨β,hβ⟩ := countable_bounded_construction S hS
  have hSβ : S ⊆ Set.Iio β := fun _ hx => hβ _ hx
  exact ⟨β,pure_restrict_intermediate_subalgebra (generatedFamily base v S)
    (generatedFamily base v (Set.Iio β)) (generatedFamily_mono base v hSβ) f hf hp hu⟩

theorem generatedFamily_eventual_pure_restriction
    (base : Set A) (v : constructionCardinal.{u}.ord.ToType → A)
    (hbase : TopologicalSpace.IsSeparable base)
    (hgen : generatedFamily base v Set.univ = ⊤)
    (I : constructionCardinal.{u}.ord.ToType → Set constructionCardinal.{u}.ord.ToType)
    (hI : ∀ j, (I j).Countable)
    (hclosed : ∀ S, S.Countable → DependencyClosed I S →
      PureUEP (generatedFamily base v S).subtype)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ β : constructionCardinal.{u}.ord.ToType,
      IsPureState (restrictState (generatedFamily base v (Set.Iio β)).subtype f) := by
  obtain ⟨S,hS,hdep,hp⟩ := generatedFamily_countable_pure_restriction
    base v hbase hgen I hI f hf
  exact bounded_pure_determination base v S hS f hf.1 hp (hclosed S hS hdep _ hp)

end

section
universe u v w
variable {J : Type u} [Preorder J] {K : Type v}
    {A : Type w} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (D : J → Type w) [∀ j, CStarAlgebra (D j)]
    [∀ j, PartialOrder (D j)] [∀ j, StarOrderedRing (D j)]

theorem scheduled_pure_equivalent_to_reference
    (into : ∀ j, D j →⋆ₐ[ℂ] A) (hinj : ∀ j, Function.Injective (into j))
    (incl : ∀ {i j}, i ≤ j → D i →⋆ₐ[ℂ] D j)
    (hcomp : ∀ {i j} (h : i ≤ j), (into j).comp (incl h) = into i)
    (hu : ∀ j, PureUEP (into j))
    (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (hfp : ∀ j, IsPureState (restrictState (into j) f))
    (list : ∀ j, K → D j →L[ℂ] ℂ)
    (hlp : ∀ j η, IsPureState (list j η))
    (hex : ∀ j (g : D j →L[ℂ] ℂ), IsPureState g → ∃ η, list j η = g)
    (σ : J × K → J) (hσ : ∀ p, p.1 ≤ σ p)
    (next : J → J) (hn : ∀ j, j ≤ next j)
    (treated : ∀ j η, ∃ (G : D (next (σ (j,η))) →L[ℂ] ℂ)
      (hG : IsPureState G),
      restrictState (incl ((hσ (j,η)).trans (hn (σ (j,η))))) G = list j η ∧
      PureStateEquivalent G hG (restrictState (into (next (σ (j,η)))) f)
        (hfp (next (σ (j,η)))))
    (H : A →L[ℂ] ℂ) (hH : IsPureState H)
    (hearly : ∃ j, IsPureState (restrictState (into j) H)) :
    PureStateEquivalent H hH f hf := by
  obtain ⟨j,hj⟩ := hearly
  obtain ⟨η,hη⟩ := hex j _ hj
  obtain ⟨G,hG,hrG,heG⟩ := treated j η
  let k := next (σ (j,η))
  have hjk : j ≤ k := (hσ (j,η)).trans (hn (σ (j,η)))
  have hup : StateExtensionUnique ((into k).comp (incl hjk)) (list j η) := by
    rw [hcomp]
    exact hu j _ (hlp j η)
  have hsH : IsState (restrictState (into k) H) := isState_restrict (into k) H hH.1
  have hrH : restrictState (incl hjk) (restrictState (into k) H) = list j η := by
    rw [restrictState_comp,hcomp,hη]
  have hHG : restrictState (into k) H = G :=
    hup.of_comp (hinj k) _ _ hsH hG.1 hrH hrG
  exact pure_lifts_equivalent (into k) G (restrictState (into k) f) hG (hfp k)
    heG (hu k _ (hfp k)) H f hH hf hHG rfl

end

open scoped ComplexOrder CStarAlgebra
section
variable {B : Type*} [CStarAlgebra B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_nontrivial_space (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) : Nontrivial H := by
  classical
  by_contra hn
  have : Subsingleton H := not_nontrivial_iff_subsingleton.mp hn
  apply hπ.1
  ext a x
  exact Subsingleton.elim _ _

theorem car_no_finite_irreps (φ : CAR →⋆ₐ[ℂ] B)
    (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) : ¬ Module.Finite ℂ H := by
  intro hf
  let := hf
  let := irreducible_nontrivial_space π hπ
  let ρ := π.comp φ.toNonUnitalStarAlgHom
  have hρ : ρ ≠ 0 := by
    intro hz
    have he := congrArg (fun f : CAR →⋆ₙₐ[ℂ] (H →L[ℂ] H) => f 1) hz
    have : (1 : H →L[ℂ] H) = 0 := by
      change π (φ 1) = 0 at he
      simpa only [map_one,irreducible_map_one π hπ] using he
    exact one_ne_zero this
  have hi := simple_nonzeroStarHom_injective carSimple ρ hρ
  let F : CAR →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := ρ
      map_add' := map_add ρ
      map_smul' := fun c a => map_smul ρ c a }
  exact carInfiniteDimensional (Module.Finite.of_injective F hi)

end

open scoped ComplexOrder CStarAlgebra InnerProductSpace
section
universe u v w
variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem UnitarilyEquivalent.isIrreducible
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (he : UnitarilyEquivalent π ρ) (hπ : IsIrreducible π) : IsIrreducible ρ := by
  obtain ⟨U,hU⟩ := he
  refine ⟨?_,fun M hM hinv => ?_⟩
  · intro hz
    apply hπ.1
    ext a x
    apply U.injective
    simpa only [hz,NonUnitalStarAlgHom.zero_apply,zero_apply,map_zero] using hU a x
  · let N : Submodule ℂ H := M.comap U.toLinearEquiv.toLinearMap
    have hN : IsClosed (N : Set H) := hM.preimage U.continuous
    have hNi (a : A) (x : H) (hx : x ∈ N) : π a x ∈ N := by
      change U (π a x) ∈ M
      rw [hU]
      exact hinv a (U x) hx
    rcases hπ.2 N hN hNi with hb | ht
    · left
      apply bot_unique
      intro y hy
      change y = 0
      have hx : U.symm y ∈ N := by
        change U (U.symm y) ∈ M
        simpa only [U.apply_symm_apply] using hy
      have hz : U.symm y = 0 := by simpa only [hb,Submodule.mem_bot] using hx
      rw [← U.apply_symm_apply y,hz,map_zero]
    · right
      apply top_unique
      intro y _
      have hx : U.symm y ∈ N := by rw [ht]; trivial
      change U (U.symm y) ∈ M at hx
      simpa only [U.apply_symm_apply] using hx

variable [PartialOrder A] [StarOrderedRing A]

theorem irreducible_vector_pure_equivalent
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) :
    ∃ hf : IsPureState (vectorFunctional π ξ),
      UnitarilyEquivalent (pureGNS (vectorFunctional π ξ) hf) π := by
  have hs := irreducible_vector_state π hπ ξ hξ
  have hn : ξ ≠ 0 := by
    intro h
    have hz : (0:ℝ) = 1 := by simpa only [h,norm_zero] using hξ
    exact zero_ne_one hz
  have he := cyclic_representation_equivalent (positiveOfSquares (vectorFunctional π ξ) hs.2)
    π ξ (fun _ => rfl) (irreducible_vector_cyclic π hπ ξ hn)
  have hp := isPureState_of_gns_irreducible (vectorFunctional π ξ) hs
    (he.symm.isIrreducible hπ)
  exact ⟨hp,he⟩

theorem all_irreducibles_equivalent_of_pure_states
    (hall : ∀ (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ) :
    UnitarilyEquivalent π ρ := by
  let := irreducible_nontrivial_space π hπ
  let := irreducible_nontrivial_space ρ hρ
  obtain ⟨ξ,hξ⟩ := exists_norm_eq H (show (0:ℝ) ≤ 1 by norm_num)
  obtain ⟨η,hη⟩ := exists_norm_eq K (show (0:ℝ) ≤ 1 by norm_num)
  obtain ⟨hf,hfπ⟩ := irreducible_vector_pure_equivalent π hπ ξ hξ
  obtain ⟨hg,hgρ⟩ := irreducible_vector_pure_equivalent ρ hρ η hη
  exact hfπ.symm.trans ((hall _ _ hf hg).trans hgρ)

end

open Filter Topology
open scoped CStarAlgebra
section
namespace HNNWord
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

def AllCoefficients (S : Set A) : HNNWord A → Prop
  | .single _ a => a ∈ S
  | .cons _ a w => a ∈ S ∧ w.AllCoefficients S

theorem reduced_approximation (φ : A →⋆ₐ[ℂ] C) (v : Bool → C)
    (S : Set A) (hS : Dense S) (K : Bool → A → Prop)
    (center : Bool → A →L[ℂ] A)
    (hc : ∀ i a, K i (center i a))
    (hfix : ∀ i a, K i a → center i a = a)
    (hmem : ∀ i a, a ∈ S → center i a ∈ S)
    (w : HNNWord A) (hw : w.Reduced K) :
    ∃ u : ℕ → HNNWord A, (∀ n, (u n).first = w.first) ∧
      (∀ n, (u n).Reduced K) ∧ (∀ n, (u n).AllCoefficients S) ∧
      Tendsto (fun n => (u n).eval φ v) atTop (𝓝 (w.eval φ v)) := by
  induction w with
  | single i a =>
    obtain ⟨b,hb,ht⟩ := mem_closure_iff_seq_limit.mp (hS a)
    refine ⟨fun n => .single i (b n),fun _ => rfl,fun _ => trivial,hb,?_⟩
    exact tendsto_const_nhds.mul ((map_continuous φ).tendsto a |>.comp ht)
  | cons i a w ih =>
    obtain ⟨u,hu₁,hu₂,hu₃,hu₄⟩ := ih hw.2
    obtain ⟨b,hb,ht⟩ := mem_closure_iff_seq_limit.mp (hS a)
    by_cases hi : i = w.first
    · refine ⟨fun n => .cons i (b n) (u n),fun _ => rfl,
        fun n => ⟨Or.inl (hi.trans (hu₁ n).symm),hu₂ n⟩,
        fun n => ⟨hb n,hu₃ n⟩,?_⟩
      exact (tendsto_const_nhds.mul ((map_continuous φ).tendsto a |>.comp ht)).mul hu₄
    · have ha : K i a := hw.1.resolve_left hi
      refine ⟨fun n => .cons i (center i (b n)) (u n),fun _ => rfl,
        fun n => ⟨Or.inr (hc i (b n)),hu₂ n⟩,
        fun n => ⟨hmem i (b n) (hb n),hu₃ n⟩,?_⟩
      have ht' : Tendsto (fun n => center i (b n)) atTop (𝓝 a) := by
        simpa only [hfix i a ha,Function.comp_def] using (center i).continuous.tendsto a |>.comp ht
      exact (tendsto_const_nhds.mul ((map_continuous φ).tendsto a |>.comp ht')).mul hu₄
end HNNWord

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem hnn_reduced_vanish_of_dense (φ : A →⋆ₐ[ℂ] C) (v : Bool → C)
    (S : Set A) (hS : Dense S) (K : Bool → A → Prop)
    (center : Bool → A →L[ℂ] A)
    (hc : ∀ i a, K i (center i a))
    (hfix : ∀ i a, K i a → center i a = a)
    (hmem : ∀ i a, a ∈ S → center i a ∈ S)
    (f : C →L[ℂ] ℂ)
    (hz : ∀ (u : HNNWord A) a, u.Reduced K → u.AllCoefficients S → a ∈ S →
      f (φ a*u.eval φ v) = 0)
    (w : HNNWord A) (a : A) (hw : w.Reduced K) : f (φ a*w.eval φ v) = 0 := by
  obtain ⟨u,_,hu₂,hu₃,hu₄⟩ := w.reduced_approximation φ v S hS K center hc hfix hmem hw
  obtain ⟨b,hb,ht⟩ := mem_closure_iff_seq_limit.mp (hS a)
  have ht' := f.continuous.tendsto _ |>.comp (((map_continuous φ).tendsto a |>.comp ht).mul hu₄)
  apply tendsto_nhds_unique ht'
  simpa only [Function.comp_def,hz _ _ (hu₂ _) (hu₃ _) (hb _)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))

end

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

def turnCenterCLM (i : Bool) : A →L[ℂ] A :=
  ContinuousLinearMap.id ℂ A - (starAlgHomCLM (B.diagonal (!i))).comp
    ((B.input false).expectation (!i))

@[simp] theorem turnCenterCLM_apply (i : Bool) (a : A) :
    B.turnCenterCLM i a = B.turnCenter i a := rfl

theorem turnCenter_fix (i : Bool) (a : A) (ha : B.turnCentered i a) :
    B.turnCenter i a = a := by
  change (B.input false).expectation (!i) a = 0 at ha
  simp only [turnCenter,ha,map_zero,sub_zero]

theorem hnn_limit_comparison {C : Type*} [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (hw : ∀ i, star (w i) = w (!i))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (B.turnCenter i a)*w (!i) +
      ψ (B.turnRemainder i a))
    (g : C →L[ℂ] ℂ) (hgs : IsState g)
    (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hbase : ∀ a, g (ψ a) = B.trace a)
    (S : Set A) (hS : Dense S)
    (hmem : ∀ i a, a ∈ S → B.turnCenter i a ∈ S)
    (hz : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      u.AllCoefficients S → a ∈ S → g (ψ a*u.eval ψ w) = 0)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] C,
      (∀ a, e (B.hnnBase a) = ψ a) ∧ (∀ i, e (B.hnnLetter i) = w i) ∧
      (∀ b, g (e b) = B.hnnTrace b) := by
  have hred (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered) :
      g (ψ a*u.eval ψ w) = 0 :=
    hnn_reduced_vanish_of_dense ψ w S hS B.turnCentered B.turnCenterCLM
      B.turnCenter_centered B.turnCenter_fix hmem g hz u a hu
  obtain ⟨F,hF,hFb,hFw,hFg,hFr⟩ := B.hnn_restriction ψ w hw hr
    (positiveOfSquares g hgs.2) hg hbase hred
  have hs : Function.Surjective F := by
    intro c
    have hc : c ∈ hnnGenerated ψ w := hd c
    rw [← hFr] at hc
    exact hc
  exact ⟨StarAlgEquiv.ofBijective F ⟨hF,hs⟩,hFb,hFw,hFg⟩

end PeakingPairData

open Filter Topology
section

theorem isometry_cauchy_on_dense {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : ℕ → X → Y) (hf : ∀ n, Isometry (f n))
    (s : Set X) (hs : Dense s) (hc : ∀ x ∈ s, CauchySeq (fun n => f n x))
    (x : X) : CauchySeq (fun n => f n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp (hs x) (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hc y hy) (ε/3) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have h₁ := (hf m).dist_eq x y
  have h₂ := (hf n).dist_eq y x
  have ht := dist_triangle4 (f m x) (f m y) (f n y) (f n x)
  rw [h₁,h₂,dist_comm y x] at ht
  have hmid := hN m hm n hn
  linarith

variable {A : Type*} [CStarAlgebra A]
  (α : ℕ → A ≃⋆ₐ[ℂ] A)
  (hc : ∀ a, CauchySeq (fun n => α n a))

def autPointwiseLimit (a : A) : A :=
  Classical.choose (cauchySeq_tendsto_of_complete (hc a))

theorem tendsto_autPointwiseLimit (a : A) :
    Tendsto (fun n => α n a) atTop (𝓝 (autPointwiseLimit α hc a)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hc a))

theorem autPointwiseLimit_isometry : Isometry (autPointwiseLimit α hc) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  apply tendsto_nhds_unique ((tendsto_autPointwiseLimit α hc a).dist
    (tendsto_autPointwiseLimit α hc b))
  simpa only [fun n => (StarAlgEquiv.isometry (α n)).dist_eq a b] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => dist a b) atTop (𝓝 (dist a b)))

def autLimitHom : A →⋆ₐ[ℂ] A where
  toFun := autPointwiseLimit α hc
  map_zero' := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc 0)
    (by simpa only [map_zero] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (0:A)) atTop (𝓝 0)))
  map_one' := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc 1)
    (by simpa only [map_one] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (1:A)) atTop (𝓝 1)))
  map_add' a b := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (a+b))
    (by simpa only [map_add] using ((tendsto_autPointwiseLimit α hc a).add (tendsto_autPointwiseLimit α hc b)))
  map_mul' a b := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (a*b))
    (by simpa only [map_mul] using ((tendsto_autPointwiseLimit α hc a).mul (tendsto_autPointwiseLimit α hc b)))
  commutes' z := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (algebraMap ℂ A z))
    (by simpa only [AlgHomClass.commutes] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => algebraMap ℂ A z) atTop (𝓝 (algebraMap ℂ A z))))
  map_star' a := tendsto_nhds_unique (tendsto_autPointwiseLimit α hc (star a))
    (by simpa only [map_star] using (tendsto_autPointwiseLimit α hc a).star)

theorem autLimitHom_surjective (hi : ∀ a, CauchySeq (fun n => (α n).symm a)) :
    Function.Surjective (autLimitHom α hc) := by
  intro a
  let b := autPointwiseLimit (fun n => (α n).symm) hi a
  refine ⟨b,?_⟩
  have hleft := (tendsto_autPointwiseLimit α hc b).dist
    (tendsto_const_nhds (x := a))
  have hright := (tendsto_const_nhds (x := b)).dist
    (tendsto_autPointwiseLimit (fun n => (α n).symm) hi a)
  have he (n : ℕ) : dist (α n b) a = dist b ((α n).symm a) := by
    rw [← (StarAlgEquiv.isometry (α n)).dist_eq b ((α n).symm a),(α n).apply_symm_apply]
  have hz : dist (autPointwiseLimit α hc b) a = 0 := by
    have hh := tendsto_nhds_unique hleft (hright.congr' (Filter.Eventually.of_forall
      (fun n => (he n).symm)))
    simpa only [show autPointwiseLimit (fun n => (α n).symm) hi a = b from rfl,dist_self] using hh
  exact dist_eq_zero.mp hz

def autLimitEquiv (hi : ∀ a, CauchySeq (fun n => (α n).symm a)) : A ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofBijective (autLimitHom α hc)
    ⟨(autPointwiseLimit_isometry α hc).injective,autLimitHom_surjective α hc hi⟩

theorem autLimitEquiv_transports (hi : ∀ a, CauchySeq (fun n => (α n).symm a))
    (f g : A →L[ℂ] ℂ)
    (hstate : ∀ a, Tendsto (fun n => f (α n a)) atTop (𝓝 (g a))) (a : A) :
    f (autLimitEquiv α hc hi a) = g a := by
  exact tendsto_nhds_unique (f.continuous.tendsto _ |>.comp
    (tendsto_autPointwiseLimit α hc a)) (hstate a)

end

open Filter Topology
section

theorem cauchySeq_of_tail_geometric_steps {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (k : ℕ)
    (h : ∀ n, k ≤ n → dist (x n) (x (n+1)) ≤ (1/2:ℝ)^n) : CauchySeq x := by
  rw [← cauchySeq_shift k]
  apply cauchySeq_of_le_geometric (1/2) ((1/2)^k) (by norm_num)
  intro n
  have hh := h (n+k) (Nat.le_add_left k n)
  simpa only [pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,mul_comm] using hh

variable {A : Type*} [CStarAlgebra A]

theorem exists_automorphism_of_geometric_approximants
    (q : ℕ → A) (hq : DenseRange q) (α : ℕ → A ≃⋆ₐ[ℂ] A)
    (hforward : ∀ n k, k ≤ n → dist (α n (q k)) (α (n+1) (q k)) ≤ (1/2:ℝ)^n)
    (hbackward : ∀ n k, k ≤ n →
      dist ((α n).symm (q k)) ((α (n+1)).symm (q k)) ≤ (1/2:ℝ)^n)
    (f g : A →L[ℂ] ℂ)
    (hstate : ∀ n k, k ≤ n → dist (f (α n (q k))) (g (q k)) ≤ (1/2:ℝ)^n) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a := by
  have hc : ∀ a, CauchySeq (fun n => α n a) := by
    apply isometry_cauchy_on_dense (fun n a => α n a)
      (fun n => StarAlgEquiv.isometry (α n)) (Set.range q) hq
    rintro a ⟨k,rfl⟩
    exact cauchySeq_of_tail_geometric_steps _ k (fun n hn => hforward n k hn)
  have hi : ∀ a, CauchySeq (fun n => (α n).symm a) := by
    apply isometry_cauchy_on_dense (fun n a => (α n).symm a)
      (fun n => StarAlgEquiv.isometry (α n).symm) (Set.range q) hq
    rintro a ⟨k,rfl⟩
    exact cauchySeq_of_tail_geometric_steps _ k (fun n hn => hbackward n k hn)
  let γ := autLimitEquiv α hc hi
  have hg (k : ℕ) : Tendsto (fun n => f (α n (q k))) atTop (𝓝 (g (q k))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (eventually_atTop.mpr ⟨k,fun n hn => hstate n k hn⟩)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have he : (fun a => f (γ a)) = g := by
    apply hq.equalizer (f.continuous.comp (StarAlgEquiv.isometry γ).continuous) g.continuous
    funext k
    exact tendsto_nhds_unique (f.continuous.tendsto _ |>.comp
      (tendsto_autPointwiseLimit α hc (q k))) (hg k)
  exact ⟨γ,fun a => congrFun he a⟩

end

section

universe u
open Set Cardinal Ordinal

def ordinalMajorant (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  max (f o) (⨆ x : o.ToType, ordinalMajorant f (x : Ordinal) + 1)
termination_by o
decreasing_by exact x.toOrd.property

theorem le_ordinalMajorant (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) :
    f o ≤ ordinalMajorant f o := by
  rw [ordinalMajorant]
  exact le_max_left _ _

theorem ordinalMajorant_strictMono (f : Ordinal.{u} → Ordinal.{u}) :
    StrictMono (ordinalMajorant f) := by
  intro a b hab
  conv_rhs => rw [ordinalMajorant]
  apply lt_of_lt_of_le ?_ (le_max_right _ _)
  have h := Ordinal.lt_iSup_add_one
    (fun x : b.ToType => ordinalMajorant f (x : Ordinal)) (Ordinal.ToType.mk ⟨a,hab⟩)
  simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using h

theorem ordinalMajorant_lt (c : Cardinal.{u}) (hc : c.IsRegular)
    (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ o < c.ord, f o < c.ord)
    {o : Ordinal.{u}} (ho : o < c.ord) : ordinalMajorant f o < c.ord := by
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    rw [ordinalMajorant]
    apply max_lt (hf o ho)
    apply Ordinal.iSup_add_one_lt_of_lt_cof
    · rw [Cardinal.mk_toType,hc.cof_ord]
      exact Cardinal.lt_ord.mp ho
    · intro x
      exact ih (x : Ordinal) x.toOrd.property (x.toOrd.property.trans ho)

theorem exists_injective_above (c : Cardinal.{u}) (hc : c.IsRegular)
    (f : c.ord.ToType → c.ord.ToType) :
    ∃ s : c.ord.ToType → c.ord.ToType, Function.Injective s ∧ ∀ x, f x ≤ s x := by
  classical
  let F (o : Ordinal.{u}) : Ordinal.{u} :=
    if h : o < c.ord then (f (Ordinal.ToType.mk ⟨o,h⟩) : Ordinal) else 0
  have hF (o : Ordinal.{u}) (ho : o < c.ord) : F o < c.ord := by
    simp only [F,dite_eq_left ho]
    exact (f (Ordinal.ToType.mk ⟨o,ho⟩)).toOrd.property
  let s (x : c.ord.ToType) : c.ord.ToType := Ordinal.ToType.mk
    ⟨ordinalMajorant F (x : Ordinal),ordinalMajorant_lt c hc F hF x.toOrd.property⟩
  refine ⟨s,?_,?_⟩
  · intro x y hxy
    have h := congrArg (fun z : c.ord.ToType => (z : Ordinal)) hxy
    have h' : ordinalMajorant F (x : Ordinal) = ordinalMajorant F (y : Ordinal) := by
      simpa only [s,Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using h
    have he := (ordinalMajorant_strictMono F).injective h'
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext he)
  · intro x
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    change (f x).toOrd.val ≤ (s x).toOrd.val
    simp only [s,Ordinal.ToType.toOrd,OrderIso.symm_apply_apply]
    have h := le_ordinalMajorant F (x : Ordinal)
    have hFx : F (x : Ordinal) = (f x : Ordinal) := by
      simp only [F, dite_eq_left (show (x : Ordinal) < c.ord from x.toOrd.property)]
      exact congrArg (fun z : c.ord.ToType => (f z : Ordinal))
        (OrderIso.apply_symm_apply Ordinal.ToType.mk x)
    rw [hFx] at h
    exact h

theorem exists_pair_schedule (c : Cardinal.{u}) (hc : c.IsRegular) :
    ∃ σ : c.ord.ToType × c.ord.ToType → c.ord.ToType,
      Function.Injective σ ∧ ∀ p, p.1 ≤ σ p := by
  have he : Cardinal.mk (c.ord.ToType × c.ord.ToType) = Cardinal.mk c.ord.ToType := by
    rw [Cardinal.mk_prod,Cardinal.mk_ord_toType,Cardinal.lift_id,Cardinal.mul_eq_self hc.aleph0_le]
  let e : (c.ord.ToType × c.ord.ToType) ≃ c.ord.ToType :=
    Classical.choice (Cardinal.eq.mp he)
  obtain ⟨s,hs,hbound⟩ := exists_injective_above c hc (fun x => (e.symm x).1)
  exact ⟨s ∘ e,hs.comp e.injective,fun p => by simpa using hbound (e p)⟩

end

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pure_state_finite_excision (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : A, 0 ≤ x ∧ ‖x‖ = 1 ∧ f x = 1 ∧
      ∀ a ∈ F, ‖x * (a - f a • (1:A)) * x‖ < ε := by
  let g := positiveOfSquares f hf.1.2
  let π := g.gnsNonUnitalStarAlgHom
  let ξ := gnsVector g
  have hg : g 1 = 1 := ((isState_iff f).mp hf.1).1
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one g hg
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hcoeff (b : A) : ⟪ξ,π b ξ⟫_ℂ = f b := gnsVector_coefficient g b
  have hs : ∀ᶠ e : ExcisionIndex (vectorNullAlgebra π ξ) in atTop,
      ∀ a ∈ F, ‖pureExcisionNet π ξ e * (a - f a • (1:A)) *
        pureExcisionNet π ξ e‖ < ε := by
    apply (F.eventually_all).mpr
    intro a _
    have hh := (pureExcisionNet_excision π hπ ξ hξ a).norm
    simpa only [hcoeff,norm_zero] using (tendsto_order.mp hh).2 ε (by simpa using hε)
  obtain ⟨e,he⟩ := hs.exists
  let x := pureExcisionNet π ξ e
  have hx : f x = 1 := by
    rw [← hcoeff,pureExcisionNet_fixes π (irreducible_map_one π hπ)]
    simp only [inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  refine ⟨x,pureExcisionNet_nonneg π ξ e,le_antisymm (pureExcisionNet_norm π ξ e) ?_,hx,he⟩
  have hh := f.le_opNorm x
  rw [hf.1.1,hx,norm_one,one_mul] at hh
  exact hh

omit [PartialOrder A] [StarOrderedRing A] in

theorem compressed_vector_coefficient_bound
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : A) (hx : IsSelfAdjoint x) (ζ : H) (hζ : ‖ζ‖ ≤ 1)
    (hy : 0 < ‖π x ζ‖) (a : A) (c : ℂ) :
    ‖⟪(‖π x ζ‖:ℂ)⁻¹ • π x ζ, π a ((‖π x ζ‖:ℂ)⁻¹ • π x ζ)⟫_ℂ - c‖ ≤
      ‖π x ζ‖⁻¹^2 * ‖x*(a-c • (1:A))*x‖ := by
  let y := π x ζ
  let η := (‖y‖:ℂ)⁻¹ • y
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y)]
    exact inv_mul_cancel₀ (show ‖y‖ ≠ 0 from hy.ne')
  have he : ⟪η,π a η⟫_ℂ - c = ⟪η,π (a-c • (1:A)) η⟫_ℂ := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,hone,one_apply_eq_self,
      inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hη]
    norm_num
  have hcompress : ⟪y,π (a-c • (1:A)) y⟫_ℂ = ⟪ζ,π (x*(a-c • (1:A))*x) ζ⟫_ℂ := by
    simp only [y,map_mul,mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_right (π x),← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,hx.star_eq]
  have hb : ‖⟪ζ,π (x*(a-c • (1:A))*x) ζ⟫_ℂ‖ ≤ ‖x*(a-c • (1:A))*x‖ := by
    exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.le_opNorm _ ζ) (norm_nonneg ζ)).trans (by
        have hn := NonUnitalStarAlgHom.norm_apply_le π (x*(a-c • (1:A))*x)
        calc
          ‖ζ‖ * (‖π (x*(a-c • (1:A))*x)‖ * ‖ζ‖) ≤
            1 * (‖x*(a-c • (1:A))*x‖ * 1) := by gcongr
          _ = _ := by ring))
  change ‖⟪η,π a η⟫_ℂ - c‖ ≤ _
  rw [he]
  simp only [η,map_smul,inner_smul_left,inner_smul_right,norm_mul,RCLike.norm_conj,
    norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y),hcompress]
  calc
    ‖y‖⁻¹ * (‖y‖⁻¹ * ‖⟪ζ,π (x*(a-c • (1:A))*x) ζ⟫_ℂ‖) ≤
      ‖y‖⁻¹ * (‖y‖⁻¹ * ‖x*(a-c • (1:A))*x‖) := by gcongr
    _ = _ := by ring

theorem faithful_vector_pure_approximation
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (hi : Function.Injective π)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : H, ‖η‖ = 1 ∧ ∀ a ∈ F, ‖⟪η,π a η⟫_ℂ - f a‖ < ε := by
  obtain ⟨x,hx,hxn,hfx,hsmall⟩ := pure_state_finite_excision f hf F (ε/4) (by positivity)
  have hnorm : ‖π x‖ = 1 := by
    rw [(NonUnitalStarAlgHom.isometry π hi).norm_map_of_map_zero (map_zero π),hxn]
  obtain ⟨ζ,hζ,hζx⟩ := (π x).exists_lt_apply_of_lt_opNorm (r := 1/2) (by rw [hnorm]; norm_num)
  let η := (‖π x ζ‖:ℂ)⁻¹ • π x ζ
  have hy : 0 < ‖π x ζ‖ := lt_trans (by norm_num) hζx
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hy.ne']
  refine ⟨η,hη,fun a ha => ?_⟩
  have hb := compressed_vector_coefficient_bound π hone x (IsSelfAdjoint.of_nonneg hx)
    ζ hζ.le hy a (f a)
  change ‖⟪η,π a η⟫_ℂ - f a‖ ≤ _ at hb
  have hinv : ‖π x ζ‖⁻¹ ≤ 2 := by
    have hh : (1/2:ℝ)⁻¹ = 2 := by norm_num
    rw [← hh]
    exact (inv_le_inv₀ hy (show 0 < (1/2:ℝ) by norm_num)).mpr hζx.le
  calc
    _ ≤ ‖π x ζ‖⁻¹^2 * ‖x*(a-f a • (1:A))*x‖ := hb
    _ ≤ 4 * ‖x*(a-f a • (1:A))*x‖ := by
      gcongr
      nlinarith [inv_nonneg.mpr hy.le]
    _ < 4*(ε/4) := by gcongr; exact hsmall a ha
    _ = ε := by ring

theorem simple_pure_inner_orbit_finite
    (hA : IsSimpleCStar A) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary A, ∀ a ∈ F, ‖⟪ξ,π (star (u:A)*a*(u:A)) ξ⟫_ℂ - f a‖ < ε := by
  obtain ⟨η,hη,he⟩ := faithful_vector_pure_approximation π (irreducible_map_one π hπ)
    (simple_nonzeroStarHom_injective hA π hπ.1) f hf F ε hε
  obtain ⟨u,hu⟩ := irreducible_unitary_vector π hπ ξ η (hξ.trans hη.symm)
  refine ⟨u,fun a ha => ?_⟩
  simpa only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,hu] using he a ha

end

open Filter Topology
open scoped InnerProductSpace
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_inner_geometric_state_approximants (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) (q : ℕ → A) :
    ∃ u : ℕ → unitary A, ∀ n k, k ≤ n →
      dist (f ((Unitary.conjStarAlgAut ℂ A (u n)).symm (q k))) (g (q k)) ≤ (1/2:ℝ)^n := by
  classical
  let F := positiveOfSquares f hf.1.2
  let π := F.gnsNonUnitalStarAlgHom
  let ξ := gnsVector F
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1
  have hs (n : ℕ) : ∃ u : unitary A, ∀ k ≤ n,
      dist (f ((Unitary.conjStarAlgAut ℂ A u).symm (q k))) (g (q k)) ≤ (1/2:ℝ)^n := by
    obtain ⟨u,hu⟩ := simple_pure_inner_orbit_finite hA π hπ ξ hξ g hg
      ((Finset.range (n+1)).image q) ((1/2:ℝ)^n) (pow_pos (by norm_num) _)
    refine ⟨u,fun k hk => ?_⟩
    have hh := hu (q k) (Finset.mem_image.mpr
      ⟨k,Finset.mem_range.mpr (Nat.lt_succ_of_le hk),rfl⟩)
    have hc : ⟪ξ,π (star (u:A)*q k*(u:A)) ξ⟫_ℂ = f (star (u:A)*q k*(u:A)) :=
      gnsVector_coefficient F _
    rw [dist_eq_norm]
    change ‖f (star (u:A)*q k*(u:A)) - g (q k)‖ ≤ _
    rw [← hc]
    exact hh.le
  exact ⟨fun n => Classical.choose (hs n),fun n => Classical.choose_spec (hs n)⟩

end

open Topology
section
variable {A ι κ : Type*} [CStarAlgebra A]

theorem generatedFamily_iUnion_directed [Nonempty κ]
    (base : Set A) (v : ι → A) (N : κ → Set ι) (hN : Directed (· ⊆ ·) N) :
    (generatedFamily base v (⋃ k, N k) : Set A) =
      closure (⋃ k, (generatedFamily base v (N k) : Set A)) := by
  let C : StarSubalgebra ℂ A := (⨆ k, generatedFamily base v (N k)).topologicalClosure
  have hd : Directed (· ≤ ·) (fun k => generatedFamily base v (N k)) :=
    fun i j => by
      obtain ⟨k,hik,hjk⟩ := hN i j
      exact ⟨k,generatedFamily_mono base v hik,generatedFamily_mono base v hjk⟩
  have hcoe : (C : Set A) = closure (⋃ k, (generatedFamily base v (N k) : Set A)) := by
    change closure (((⨆ k, generatedFamily base v (N k)) : StarSubalgebra ℂ A) : Set A) = _
    rw [StarSubalgebra.coe_iSup_of_directed hd]
  apply Set.Subset.antisymm
  · rw [← hcoe]
    change generatedFamily base v (⋃ k, N k) ≤ C
    apply StarSubalgebra.topologicalClosure_minimal _
      (show IsClosed (C : Set A) from isClosed_closure)
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | ⟨j,hj,rfl⟩
    · let k : κ := Classical.arbitrary κ
      exact subset_closure ((le_iSup (fun k => generatedFamily base v (N k)) k)
        (generatedFamily_contains_base base v (N k) hx))
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hj
      exact subset_closure ((le_iSup (fun k => generatedFamily base v (N k)) k)
        (generatedFamily_contains base v hk))
  · apply closure_minimal _ (generatedFamily_isClosed base v _)
    exact Set.iUnion_subset fun k => generatedFamily_mono base v (Set.subset_iUnion N k)

universe u

theorem generatedFamily_ordinal_continuous (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (j : Ordinal.{u}) (hj : Order.IsSuccLimit j) :
    (generatedFamily base v (S ∪ Set.Iio j) : Set A) =
      closure (⋃ k : {k : Ordinal.{u} // k < j},
        (generatedFamily base v (S ∪ Set.Iio k.val) : Set A)) := by
  let K := {k : Ordinal.{u} // k < j}
  have h0 : (0 : Ordinal.{u}) < j := hj.ne_bot.bot_lt
  let : Nonempty K := ⟨⟨0,h0⟩⟩
  have hd : Directed (· ⊆ ·) (fun k : K => S ∪ Set.Iio k.val) := by
    intro k l
    refine ⟨⟨max k.val l.val,max_lt k.property l.property⟩,?_,?_⟩
    · apply Set.union_subset_union_right
      intro x hx
      change x < max k.val l.val
      exact lt_of_lt_of_le hx (le_max_left k.val l.val)
    · apply Set.union_subset_union_right
      intro x hx
      change x < max k.val l.val
      exact lt_of_lt_of_le hx (le_max_right k.val l.val)
  have he : (⋃ k : K, S ∪ Set.Iio k.val) = S ∪ Set.Iio j := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      rcases hk with hs | hx
      · exact Or.inl hs
      · exact Or.inr (hx.trans k.property)
    · intro hx
      rcases hx with hs | hx
      · exact Set.mem_iUnion.mpr ⟨⟨0,h0⟩,Or.inl hs⟩
      · exact Set.mem_iUnion.mpr ⟨⟨Order.succ x,hj.succ_lt hx⟩,Or.inr (Order.lt_succ x)⟩
  rw [← he]
  exact generatedFamily_iUnion_directed base v _ hd

theorem dense_iUnion_starSubalgebra_inclusions
    (S : StarSubalgebra ℂ A) (T : κ → StarSubalgebra ℂ A) (hT : ∀ k, T k ≤ S)
    (he : (S : Set A) = closure (⋃ k, (T k : Set A))) :
    Dense (⋃ k, Set.range (StarSubalgebra.inclusion (hT k))) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx : (x:A) ∈ closure (⋃ k, (T k : Set A)) := by rw [← he]; exact x.property
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hy
  refine ⟨⟨y,hT k hk⟩,Set.mem_iUnion.mpr ⟨k,⟨y,hk⟩,rfl⟩,?_⟩
  exact hxy

end

open Topology
section
attribute [local instance] generatedFamily_isClosed
universe u
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (base : Set A) (v : Ordinal.{u} → A) (S : Set Ordinal.{u})

omit [PartialOrder A] [StarOrderedRing A] in
theorem starSubalgebra_inclusion_comp (X Y Z : StarSubalgebra ℂ A)
    (h : X ≤ Y) (h' : Y ≤ Z) :
    (StarSubalgebra.inclusion h').comp (StarSubalgebra.inclusion h) =
      StarSubalgebra.inclusion (h.trans h') := rfl

def retainedOrdinalAlgebra (j : Ordinal.{u}) : StarSubalgebra ℂ A :=
  generatedFamily base v (S ∪ Set.Iio j)

instance retainedOrdinalAlgebra_isClosed (j : Ordinal.{u}) :
    IsClosed (retainedOrdinalAlgebra base v S j : Set A) := generatedFamily_isClosed _ _ _

private noncomputable instance retainedOrdinalAlgebra_cstar (j : Ordinal.{u}) :
    CStarAlgebra (retainedOrdinalAlgebra base v S j) :=
  StarSubalgebra.cstarAlgebra _

local instance retainedOrdinalAlgebra_order (j : Ordinal.{u}) :
    PartialOrder (retainedOrdinalAlgebra base v S j) :=
  CStarAlgebra.spectralOrder _
local instance retainedOrdinalAlgebra_starOrder (j : Ordinal.{u}) :
    StarOrderedRing (retainedOrdinalAlgebra base v S j) :=
  CStarAlgebra.spectralOrderedRing _

def retainedOrdinalInclusion {i j : Ordinal.{u}} (h : i ≤ j) :
    retainedOrdinalAlgebra base v S i →⋆ₐ[ℂ] retainedOrdinalAlgebra base v S j :=
  StarSubalgebra.inclusion (generatedFamily_mono base v (Set.union_subset_union_right S
    (fun _ hx => lt_of_lt_of_le hx h)))

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_injective {i j : Ordinal.{u}} (h : i ≤ j) :
    Function.Injective (retainedOrdinalInclusion base v S h) := by
  exact StarSubalgebra.inclusion_injective _

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_continuous (j : Ordinal.{u}) (hj : Order.IsSuccLimit j) :
    Dense (⋃ k : {k : Ordinal.{u} // k < j},
      Set.range (retainedOrdinalInclusion base v S k.property.le)) :=
  dense_iUnion_starSubalgebra_inclusions _ _ _ (generatedFamily_ordinal_continuous base v S j hj)

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_refl (j : Ordinal.{u}) :
    retainedOrdinalInclusion base v S (le_refl j) =
      StarAlgHom.id ℂ (retainedOrdinalAlgebra base v S j) := by
  ext x
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_comp {i j k : Ordinal.{u}} (h : i ≤ j) (h' : j ≤ k) :
    (retainedOrdinalInclusion base v S h').comp (retainedOrdinalInclusion base v S h) =
      retainedOrdinalInclusion base v S (h.trans h') :=
  starSubalgebra_inclusion_comp _ _ _ _ _

omit [PartialOrder A] [StarOrderedRing A] in

theorem retainedOrdinal_pureUEP (L : Ordinal.{u})
    (hbase : IsSimpleCStar (retainedOrdinalAlgebra base v S 0))
    (hnext : ∀ j < L, BridgeSuccessor
      (retainedOrdinalInclusion base v S (show j ≤ j+1 by exact le_self_add))) :
    PureUEP (retainedOrdinalInclusion base v S (show 0 ≤ L by exact bot_le)) := by
  apply bridge_ordinal_pureUEP (fun j => retainedOrdinalAlgebra base v S j)
    (fun h => retainedOrdinalInclusion base v S h) L hbase hnext
    (fun h => retainedOrdinalInclusion_injective base v S h)
    (fun j _ hj => retainedOrdinalInclusion_continuous base v S j hj)
    (retainedOrdinalInclusion_refl base v S)
    (fun h h' => retainedOrdinalInclusion_comp base v S h h') L le_rfl 0 bot_le

omit [PartialOrder A] [StarOrderedRing A] in

theorem retainedOrdinalSucc_eq_of_mem (j : Ordinal.{u}) (hj : j ∈ S) :
    retainedOrdinalAlgebra base v S (j+1) = retainedOrdinalAlgebra base v S j := by
  apply congrArg (generatedFamily base v)
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp (show x < j+1 from hx)) with hx | rfl
      · exact Or.inr hx
      · exact Or.inl hj
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (show x < j+1 from (show x < j from hx).trans_le le_self_add)

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalSuccessor_identity (j : Ordinal.{u}) (hj : j ∈ S) :
    BridgeSuccessor (retainedOrdinalInclusion base v S
      (show j ≤ j+1 by exact le_self_add)) := by
  let φ := retainedOrdinalInclusion base v S (show j ≤ j+1 by exact le_self_add)
  have hs : Function.Surjective φ := by
    intro x
    have hx : (x:A) ∈ retainedOrdinalAlgebra base v S j := by
      rw [← retainedOrdinalSucc_eq_of_mem base v S j hj]
      exact x.property
    exact ⟨⟨x,hx⟩,rfl⟩
  exact BridgeSuccessor.identity (StarAlgEquiv.ofBijective φ
    ⟨retainedOrdinalInclusion_injective base v S _,hs⟩) (fun _ => rfl)

omit [PartialOrder A] [StarOrderedRing A] in

theorem retainedOrdinal_pureUEP_of_omitted (L : Ordinal.{u})
    (hbase : IsSimpleCStar (retainedOrdinalAlgebra base v S 0))
    (hnext : ∀ j < L, j ∉ S → BridgeSuccessor
      (retainedOrdinalInclusion base v S (show j ≤ j+1 by exact le_self_add))) :
    PureUEP (retainedOrdinalInclusion base v S (show 0 ≤ L by exact bot_le)) := by
  classical
  apply retainedOrdinal_pureUEP base v S L hbase
  intro j hj
  by_cases hjs : j ∈ S
  · exact retainedOrdinalSuccessor_identity base v S j hjs
  · exact hnext j hj hjs

end

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {f g h : A →L[ℂ] ℂ} {hf : IsPureState f} {hg : IsPureState g} {hh : IsPureState h}

theorem PureStateEquivalent.symm (e : PureStateEquivalent f hf g hg) :
    PureStateEquivalent g hg f hf := UnitarilyEquivalent.symm e

theorem PureStateEquivalent.trans (e : PureStateEquivalent f hf g hg)
    (e' : PureStateEquivalent g hg h hh) : PureStateEquivalent f hf h hh :=
  UnitarilyEquivalent.trans e e'

end

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
namespace PeakingPairData

section
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

theorem hnnPush_class_exclusions (hB : B.Separated) (hA : IsSimpleCStar A)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hD : let D := Q.hnnPush B hB hA ht
      ¬ PureStateEquivalent (D.state false) (D.peaks false).isPureState
        (D.state true) (D.peaks true).isPureState) :
    (¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
      (Q.state true) (Q.peaks true).isPureState) ∧
    ∀ i, ¬ (PureStateEquivalent (B.state false) (B.peaks false).isPureState
        (Q.state i) (Q.peaks i).isPureState ∧
      PureStateEquivalent (B.state true) (B.peaks true).isPureState
        (Q.state (!i)) (Q.peaks (!i)).isPureState) := by
  let D := Q.hnnPush B hB hA ht
  let F := B.hnnPush B hB hA (fun _ => rfl)
  have hDres (i : Bool) : restrictState B.hnnBase (D.state i) = Q.state i :=
    Q.pushedState_restrict B.hnnBase B.hnnBase_injective
      (fun i => B.hnn_unique hB hA _ (Q.peaks i).isPureState) i
  have hFres (i : Bool) : restrictState B.hnnBase (F.state i) = B.state i :=
    B.pushedState_restrict B.hnnBase B.hnnBase_injective
      (fun i => B.hnn_unique hB hA _ (B.peaks i).isPureState) i
  have hFjoin : PureStateEquivalent (F.state false) (F.peaks false).isPureState
      (F.state true) (F.peaks true).isPureState :=
    B.hnn_join hB hA _ _ (F.peaks false).isPureState (F.peaks true).isPureState
      (hFres false) (hFres true)
  constructor
  · intro he
    exact hD (pure_lifts_equivalent B.hnnBase _ _ (Q.peaks false).isPureState
      (Q.peaks true).isPureState he (B.hnn_unique hB hA _ (Q.peaks true).isPureState)
      _ _ (D.peaks false).isPureState (D.peaks true).isPureState (hDres false) (hDres true))
  · intro i he
    have he0 := pure_lifts_equivalent B.hnnBase _ _ (B.peaks false).isPureState
      (Q.peaks i).isPureState he.1 (B.hnn_unique hB hA _ (Q.peaks i).isPureState)
      _ _ (F.peaks false).isPureState (D.peaks i).isPureState (hFres false) (hDres i)
    have he1 := pure_lifts_equivalent B.hnnBase _ _ (B.peaks true).isPureState
      (Q.peaks (!i)).isPureState he.2 (B.hnn_unique hB hA _ (Q.peaks (!i)).isPureState)
      _ _ (F.peaks true).isPureState (D.peaks (!i)).isPureState (hFres true) (hDres (!i))
    have heD : PureStateEquivalent (D.state i) (D.peaks i).isPureState
        (D.state (!i)) (D.peaks (!i)).isPureState :=
      PureStateEquivalent.trans (PureStateEquivalent.symm he0)
        (PureStateEquivalent.trans hFjoin he1)
    cases i
    · exact hD heD
    · exact hD (PureStateEquivalent.symm heD)

theorem hnnPush_swap_separated (hB : B.Separated) (hA : IsSimpleCStar A)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hneB : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState)
    (hD : let D := Q.hnnPush B hB hA ht
      ¬ PureStateEquivalent (D.state false) (D.peaks false).isPureState
        (D.state true) (D.peaks true).isPureState) :
    ∃ hQ : Q.Separated, (B.hnnPush Q hQ hA (fun a => (ht a).symm)).Separated := by
  have hex := B.hnnPush_class_exclusions Q hB hA ht hD
  let hQ := Q.separated_of_inequivalent hex.1
  exact ⟨hQ,B.hnnPush_separated Q hQ hA (fun a => (ht a).symm) hneB hex.2⟩

end

section
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

private theorem swap_map_of_equiv
    (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
    (e : D.HNNAlgebra ≃⋆ₐ[ℂ] E.HNNAlgebra)
    (hQ : Q.Separated) (hE : E.Separated) (hA : IsSimpleCStar A)
    (heA : ∀ a, e (D.hnnBase (B.hnnBase a)) = E.hnnBase (Q.hnnBase a))
    (heQ : ∀ i, e (D.hnnLetter i) = E.hnnBase (Q.hnnLetter i)) :
    ∃ φ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra,
      Function.Injective φ ∧ PureUEP φ ∧
      (∀ a, φ (Q.hnnBase a) = D.hnnBase (B.hnnBase a)) ∧
      (∀ i, φ (Q.hnnLetter i) = D.hnnLetter i) := by
  let φ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra := e.symm.toStarAlgHom.comp E.hnnBase
  have hU : PureUEP E.hnnBase := fun f hf => E.hnn_unique hE (Q.hnn_simple hQ hA) f hf
  refine ⟨φ,e.symm.injective.comp E.hnnBase_injective,hU.postcomp_equiv e.symm,?_,?_⟩
  · intro a
    apply e.injective
    change e (e.symm (E.hnnBase (Q.hnnBase a))) = e (D.hnnBase (B.hnnBase a))
    rw [e.apply_symm_apply]
    exact (heA a).symm
  · intro i
    apply e.injective
    change e (e.symm (E.hnnBase (Q.hnnLetter i))) = e (D.hnnLetter i)
    rw [e.apply_symm_apply]
    exact (heQ i).symm

theorem actual_omitted_swap (hB : B.Separated) (hA : IsSimpleCStar A)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hneB : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState)
    (hD : let D := Q.hnnPush B hB hA ht
      ¬ PureStateEquivalent (D.state false) (D.peaks false).isPureState
        (D.state true) (D.peaks true).isPureState) :
    let D := Q.hnnPush B hB hA ht
    ∃ φ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra,
      Function.Injective φ ∧ PureUEP φ ∧
      (∀ a, φ (Q.hnnBase a) = D.hnnBase (B.hnnBase a)) ∧
      (∀ i, φ (Q.hnnLetter i) = D.hnnLetter i) := by
  obtain ⟨hQ,hE⟩ := B.hnnPush_swap_separated Q hB hA ht hneB hD
  have hr := B.hnn_reorder Q hB hQ hA ht
  generalize hd : Q.hnnPush B hB hA ht = D at hr ⊢
  generalize he : B.hnnPush Q hQ hA (fun a => (ht a).symm) = E at hE hr
  obtain ⟨e,heA,_,heQ,_⟩ := hr
  exact swap_map_of_equiv B Q D E e hQ hE hA heA heQ

end

end PeakingPairData

end NaimarkZFC

end

end OAI
