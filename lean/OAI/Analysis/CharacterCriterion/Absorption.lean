import OAI.Analysis.CharacterCriterion.UltrapowerSaturation

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam
open Filter
open scoped Topology
namespace Intertwining
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
lemma dense_pointwise_cauchy (φ : ℕ → A →⋆ₐ[ℂ] B) (a : ℕ → A)
    (ha : DenseRange a) (hc : ∀ i, CauchySeq (fun n => φ n (a i))) :
    ∀ x, CauchySeq (fun n => φ n x) := by
  intro x
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨i,hi⟩ := Metric.denseRange_iff.mp ha x (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hc i) (ε/3) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have hdist (k : ℕ) : dist (φ k x) (φ k (a i)) ≤ dist x (a i) := by
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le (φ k) _
  have hd := dist_triangle4 (φ m x) (φ m (a i)) (φ n (a i)) (φ n x)
  have h1 := hdist m
  have h2 := hdist n
  have h3 := hN m hm n hn
  rw [dist_comm (φ n (a i)) (φ n x)] at hd
  have hi' : dist x (a i) < ε/3 := by simpa only [dist_comm] using hi
  linarith
lemma limitHom_isometry (φ : ℕ → A →⋆ₐ[ℂ] B)
    (hc : ∀ a, CauchySeq (fun n => φ n a)) (hi : ∀ n, Isometry (φ n)) :
    Isometry (limitHom φ hc) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  apply tendsto_nhds_unique ((tendsto_limitHom φ hc a).dist (tendsto_limitHom φ hc b))
  have he : (fun n => dist (φ n a) (φ n b)) = (fun _ : ℕ => dist a b) :=
    funext (fun n => (hi n).dist_eq a b)
  rw [he]
  exact tendsto_const_nhds
end Intertwining


theorem local_approximate_surjectivity {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ)
    (hlocal : ∀ (S : Finset A) (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ β : B ≃⋆ₐ[ℂ] B,
        (∀ a ∈ S, dist (β (φ a)) (φ a) < ε) ∧
        (∀ b ∈ T, ∃ a : A, dist (β (φ a)) b < ε)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  classical
  let a := TopologicalSpace.denseSeq A
  let b := TopologicalSpace.denseSeq B
  let e : ℕ → ℝ := fun n => (1/2 : ℝ)^n
  let State := (B ≃⋆ₐ[ℂ] B) × Finset A
  let Good : ℕ → State → State → Prop := fun n s t =>
    s.2 ⊆ t.2 ∧ a n ∈ t.2 ∧
    (∀ x ∈ s.2, dist (t.1 (φ x)) (s.1 (φ x)) < e n) ∧
    (∀ i ≤ n, ∃ x ∈ t.2, dist (t.1 (φ x)) (b i) < e n)
  have hex : ∀ n s, ∃ t, Good n s t := by
    intro n s
    let T : Finset B := (Finset.range (n+1)).image (fun i => s.1.symm (b i))
    obtain ⟨β,hfix,hdense⟩ := hlocal s.2 T (e n) (by dsimp [e]; positivity)
    have hw : ∀ i : Fin (n+1), ∃ x : A, dist (β (φ x)) (s.1.symm (b i)) < e n := by
      intro i
      apply hdense
      exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr i.isLt,rfl⟩
    choose w hw using hw
    refine ⟨(β.trans s.1, s.2 ∪ {a n} ∪ Finset.univ.image w), ?_⟩
    refine ⟨fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx),
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)), ?_, ?_⟩
    · intro x hx
      change dist (s.1 (β (φ x))) (s.1 (φ x)) < _
      rw [(NonUnitalStarAlgHom.isometry s.1 s.1.injective).dist_eq]
      exact hfix x hx
    · intro i hi
      let j : Fin (n+1) := ⟨i,by omega⟩
      refine ⟨w j,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),?_⟩
      change dist (s.1 (β (φ (w j)))) (b i) < _
      have hh := (NonUnitalStarAlgHom.isometry s.1 s.1.injective).dist_eq (β (φ (w j))) (s.1.symm (b i))
      rw [s.1.apply_symm_apply] at hh
      rw [hh]
      exact hw j
  let step : ℕ → State → State := fun n s => (hex n s).choose
  let state : ℕ → State := fun n => Nat.rec ((StarAlgEquiv.refl ℂ B), ∅)
    (fun k s => step k s) n
  have hstep : ∀ n, Good n (state n) (state (n+1)) := fun n => (hex n (state n)).choose_spec
  let S : ℕ → Finset A := fun n => (state n).2
  let Φ : ℕ → A →⋆ₐ[ℂ] B := fun n => (state n).1.toStarAlgHom.comp φ
  have hmono : Monotone S := monotone_nat_of_le_succ (fun n => (hstep n).1)
  have hfix : ∀ n x, x ∈ S n → dist (Φ (n+1) x) (Φ n x) < e n :=
    fun n x hx => (hstep n).2.2.1 x hx
  have hiso (n : ℕ) : Isometry (Φ n) :=
    (NonUnitalStarAlgHom.isometry (state n).1 (state n).1.injective).comp (NonUnitalStarAlgHom.isometry φ hφ)
  have hcS (k : ℕ) (x : A) (hx : x ∈ S k) :
      CauchySeq (fun n => Φ n x) := by
    apply (cauchySeq_shift k).mp
    apply cauchySeq_of_dist_le_of_summable (fun n => e (n+k))
    · intro n
      rw [dist_comm]
      simpa only [Nat.succ_add, Nat.add_succ] using (hfix (n+k) x (hmono (by omega) hx)).le
    · exact summable_geometric_two.comp_injective (add_left_injective k)
  have hc : ∀ x, CauchySeq (fun n => Φ n x) := by
    apply Intertwining.dense_pointwise_cauchy Φ a (TopologicalSpace.denseRange_denseSeq A)
    intro i
    exact hcS (i+1) (a i) (hstep i).2.1
  let f := Intertwining.limitHom Φ hc
  have hfi : Isometry f := Intertwining.limitHom_isometry Φ hc hiso
  have hdist (k : ℕ) (x : A) (hx : x ∈ S k) : dist (Φ k x) (f x) ≤ 2 * e k := by
    have ht := dist_le_tsum_of_dist_le_of_tendsto (fun n => e (n+k))
      (f := fun n => Φ (n+k) x)
      (fun n => by
        rw [dist_comm]
        simpa only [Nat.succ_add, Nat.add_succ] using (hfix (n+k) x (hmono (by omega) hx)).le)
      (summable_geometric_two.comp_injective (add_left_injective k))
      ((Intertwining.tendsto_limitHom Φ hc x).comp (tendsto_add_atTop_nat k)) 0
    simp only [zero_add] at ht
    have he : (∑' n, e (n+k)) = 2 * e k := by
      simp only [e,pow_add]
      rw [tsum_mul_right,tsum_geometric_two]
    exact ht.trans_eq he
  have hdense : DenseRange f := by
    have hsub : Set.range b ⊆ closure (Set.range f) := by
      intro y hy
      obtain ⟨i,rfl⟩ := hy
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      have he0 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
            (by norm_num : (1/2 : ℝ)<1)).const_mul 2
      obtain ⟨N,hN⟩ := eventually_atTop.mp (he0.eventually (gt_mem_nhds hε))
      let n := max N i
      obtain ⟨x,hx,hxb⟩ := (hstep n).2.2.2 i (le_max_right _ _)
      refine ⟨f x,Set.mem_range_self x,?_⟩
      have htail := hdist (n+1) x hx
      have hen : 2 * e (n+1) = e n := by dsimp [e]; rw [pow_succ]; ring
      rw [hen] at htail
      have hbound := hN n (le_max_left _ _)
      have htri := dist_triangle (f x) (Φ (n+1) x) (b i)
      rw [dist_comm (f x) (Φ (n+1) x)] at htri
      change dist (Φ (n+1) x) (b i) < e n at hxb
      change dist (b i) (f x) < ε
      rw [dist_comm (b i) (f x)]
      linarith
    intro y
    apply closure_minimal hsub isClosed_closure
    exact TopologicalSpace.denseRange_denseSeq B y
  have hsurj : Function.Surjective f := by
    have hr : IsClosed (Set.range f) := hfi.isClosedEmbedding.isClosed_range
    exact fun y => by
      have hy := hdense y
      rw [hr.closure_eq] at hy
      exact hy
  exact ⟨StarAlgEquiv.ofBijective f ⟨hfi.injective,hsurj⟩⟩
end KirchbergRordam
namespace KirchbergRordam
open Filter Topology NormUltrapower


theorem isomorphism_of_ultrapower_split_and_conjugacy
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
    (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
    (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
        dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
          (NormUltrapower.diagonal ω b) < ε) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  classical
  apply local_approximate_surjectivity φ hφ
  intro S T ε hε
  obtain ⟨u,hu⟩ := hconj (T ∪ S.image φ) ε hε
  obtain ⟨v,hv⟩ := unitary_lift ω u
  let w : ℕ → unitary B := fun n => ⟨(v : BoundedSeq B) n,
    ⟨congrArg (fun f : BoundedSeq B => f n) v.property.1,
      congrArg (fun f : BoundedSeq B => f n) v.property.2⟩⟩
  let β : ℕ → B ≃⋆ₐ[ℂ] B := fun n => Unitary.conjStarAlgAut ℂ B (w n)
  let x : B → BoundedSeq A := fun b => (Ideal.Quotient.mk_surjective (ψ b)).choose
  have hx (b : B) : quotientMap ω (x b) = ψ b :=
    (Ideal.Quotient.mk_surjective (ψ b)).choose_spec
  have hfix (a : A) (ha : a ∈ S) :
      ∀ᶠ n in (ω : Filter ℕ), dist (β n (φ a)) (φ a) < ε := by
    have h := hu (φ a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
    rw [hsplit,map_diagonal] at h
    let z : BoundedSeq B := (v : BoundedSeq B)*constantSeq (φ a)*star (v : BoundedSeq B)-constantSeq (φ a)
    have hz : ‖quotientMap ω z‖ < ε := by
      simpa only [z,map_sub,map_mul,map_star,hv,NormUltrapower.diagonal,StarAlgHom.comp_apply,dist_eq_norm,
        Unitary.conjStarAlgAut_apply,Unitary.coe_star] using h
    simp only [dist_eq_norm]
    exact eventually_norm_lt ω z ε hz
  have hdense (b : B) (hb : b ∈ T) :
      ∀ᶠ n in (ω : Filter ℕ), dist (β n (φ (x b n))) b < ε := by
    have h := hu b (Finset.mem_union_left _ hb)
    let z : BoundedSeq B := (v : BoundedSeq B)*sequenceMap φ (x b)*star (v : BoundedSeq B)-constantSeq b
    have hmap : quotientMap ω (sequenceMap φ (x b))=NormUltrapower.map φ ω (ψ b) := by
      rw [← map_mk,hx]
    have hz : ‖quotientMap ω z‖ < ε := by
      simpa only [z,map_sub,map_mul,map_star,hv,hmap,NormUltrapower.diagonal,StarAlgHom.comp_apply,dist_eq_norm,
        Unitary.conjStarAlgAut_apply,Unitary.coe_star] using h
    simp only [dist_eq_norm]
    exact eventually_norm_lt ω z ε hz
  have hallS : ∀ᶠ n in (ω : Filter ℕ), ∀ a ∈ S, dist (β n (φ a)) (φ a) < ε :=
    S.eventually_all.mpr hfix
  have hallT : ∀ᶠ n in (ω : Filter ℕ), ∀ b ∈ T, dist (β n (φ (x b n))) b < ε :=
    T.eventually_all.mpr hdense
  obtain ⟨n,hnS,hnT⟩ := (hallS.and hallT).exists
  exact ⟨β n,hnS,fun b hb => ⟨x b n,hnT b hb⟩⟩
end KirchbergRordam
namespace KirchbergRordam.SeparableReduction
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]


def stage (s : Set A) : ℕ → Set A
  | 0 => s ∪ Set.range (algebraMap ℂ A)
  | n+1 => stage s n ∪ (fun p : A×A=>p.1+p.2) '' (stage s n ×ˢ stage s n) ∪
      (fun p : A×A=>p.1*p.2) '' (stage s n ×ˢ stage s n) ∪ star '' stage s n
lemma stage_step (s : Set A) (n : ℕ) : stage s n ⊆ stage s (n+1) :=
  fun _ hx => Or.inl (Or.inl (Or.inl hx))
lemma stage_mono (s : Set A) : Monotone (stage s) := monotone_nat_of_le_succ (stage_step s)
lemma stage_separable {s : Set A} (hs : IsSeparable s) (n : ℕ) : IsSeparable (stage s n) := by
  induction n with
  | zero => exact hs.union (isSeparable_range (continuous_algebraMap ℂ A))
  | succ n ih => exact ((ih.union ((ih.prod ih).image (continuous_fst.add continuous_snd))).union
      ((ih.prod ih).image (continuous_fst.mul continuous_snd))).union (ih.image continuous_star)
def termAlgebra (s : Set A) : StarSubalgebra ℂ A where
  carrier := ⋃ n, stage s n
  zero_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨0,map_zero _⟩⟩
  one_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨1,map_one _⟩⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩))⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩)⟩
  algebraMap_mem' z := mem_iUnion.mpr ⟨0,Or.inr ⟨z,rfl⟩⟩
  star_mem' := by
    intro a ha
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨n+1,Or.inr ⟨a,hn,rfl⟩⟩
lemma adjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have ht : StarAlgebra.adjoin ℂ s ≤ termAlgebra s := StarAlgebra.adjoin_le
    (fun a ha=>mem_iUnion.mpr ⟨0,Or.inl ha⟩)
  exact (IsSeparable.iUnion (stage_separable hs)).mono ht


lemma closedAdjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set A) :=
  (adjoin_separable hs).closure
end KirchbergRordam.SeparableReduction

namespace KirchbergRordam.MaxTensor
open Topology TopologicalSpace
open scoped CStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]


theorem separable_maxTensor [SeparableSpace A] [SeparableSpace B] :
    SeparableSpace (Algebra A B) := by
  let s : Set (Algebra A B) := Set.range (includeLeft (A := A) (B := B)) ∪
    Set.range (includeRight (A := A) (B := B))
  let T := (StarAlgebra.adjoin ℂ s).topologicalClosure
  have hsep : IsSeparable (T : Set (Algebra A B)) :=
    SeparableReduction.closedAdjoin_separable ((isSeparable_range (map_continuous includeLeft)).union
      (isSeparable_range (map_continuous includeRight)))
  have hinc : s ⊆ T := (StarAlgebra.subset_adjoin ℂ s).trans
    (StarSubalgebra.le_topologicalClosure _)
  have hall (x : Algebra A B) : x ∈ T := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact StarSubalgebra.isClosed_topologicalClosure _
    | ih x =>
      change of x ∈ T
      suffices ∀ tensor : A ⊗[ℂ] B, of (rawEquiv tensor) ∈ T from
        this (rawEquiv.symm x)
      intro tensor
      induction tensor using TensorProduct.inductionOn with
      | tmul a b =>
        change of (a ⊗ₜ[ℂ] b) ∈ T
        rw [of_tmul]
        exact T.mul_mem (hinc (Or.inl ⟨a,rfl⟩)) (hinc (Or.inr ⟨b,rfl⟩))
      | add x y hx hy =>
        simp only [map_add]
        exact T.add_mem hx hy
  exact isSeparable_univ_iff.mp (hsep.mono (fun x _ => hall x))

instance powerPack_separable (D : Type*) [CStarAlgebra D] [SeparableSpace D] (n : ℕ) :
    SeparableSpace (powerPack D n) := by
  induction n with
  | zero => exact inferInstanceAs (SeparableSpace D)
  | succ n ih =>
    let := ih
    exact separable_maxTensor (A := D) (B := powerPack D n)
end KirchbergRordam.MaxTensor
namespace KirchbergRordam.MaxTensor
open Filter Topology


theorem pointwise_limit_of_tensor_legs
    {A D C : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra C]
    (F : ℕ → Algebra A D →⋆ₐ[ℂ] C) (g : Algebra A D →⋆ₐ[ℂ] C)
    (hL : ∀ a, Tendsto (fun n => F n (includeLeft a)) atTop (𝓝 (g (includeLeft a))))
    (hR : ∀ d, Tendsto (fun n => F n (includeRight d)) atTop (𝓝 (g (includeRight d)))) :
    ∀ b, Tendsto (fun n => F n b) atTop (𝓝 (g b)) := by
  have hEq : Equicontinuous (fun n b => F n b) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro b c n
    change dist (F n b) (F n c) ≤ dist b c
    rw [dist_eq_norm,← map_sub,dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le (F n) (b-c)
  have hg : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro b c
    simp only [NNReal.coe_one,one_mul]
    rw [dist_eq_norm,← map_sub,dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le g (b-c)
  have hclosed := hEq.isClosed_setOfPred_tendsto (l := atTop) hg.continuous
  intro b
  induction b using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    change Tendsto (fun n => F n (of x)) atTop (𝓝 (g (of x)))
    suffices ∀ tensor : A ⊗[ℂ] D,
        Tendsto (fun n => F n (of (rawEquiv tensor))) atTop
          (𝓝 (g (of (rawEquiv tensor)))) from this (rawEquiv.symm x)
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | tmul a d =>
      change Tendsto (fun n => F n (of (a ⊗ₜ[ℂ] d))) atTop
        (𝓝 (g (of (a ⊗ₜ[ℂ] d))))
      simpa only [of_tmul,map_mul] using (hL a).mul (hR d)
    | add x y hx hy =>
      simpa only [map_add] using hx.add hy
end KirchbergRordam.MaxTensor
namespace KirchbergRordam
open NormUltrapower
open scoped CStarAlgebra TensorProduct
lemma ultrapower_left_commutes_right
    {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
    (ω : Ultrafilter ℕ) (x : NormUltrapower.Algebra A ω) (d : D) :
    Commute (NormUltrapower.map (MaxTensor.includeLeft (B := D)) ω x)
      (NormUltrapower.diagonal ω (MaxTensor.includeRight (A := A) d)) := by
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Commute (NormUltrapower.map (MaxTensor.includeLeft (B := D)) ω (quotientMap ω y))
    (NormUltrapower.diagonal ω (MaxTensor.includeRight (A := A) d))
  rw [NormUltrapower.map_mk]
  change quotientMap ω (sequenceMap MaxTensor.includeLeft y) * quotientMap ω (constantSeq (MaxTensor.includeRight d)) =
    quotientMap ω (constantSeq (MaxTensor.includeRight d)) * quotientMap ω (sequenceMap MaxTensor.includeLeft y)
  rw [← map_mul,← map_mul]
  congr 1
  ext n
  exact (MaxTensor.legs_commute (y n) d).eq
lemma maximal_lift_image_commutes
    {A D C : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra C]
    (L : A →⋆ₐ[ℂ] C) (R : D →⋆ₐ[ℂ] C) (hcomm : ∀ a d, Commute (L a) (R d))
    (c : C) (hL : ∀ a, Commute c (L a)) (hR : ∀ d, Commute c (R d))
    (x : MaxTensor.Algebra A D) : Commute c (MaxTensor.lift L R hcomm x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.mul (map_continuous (MaxTensor.lift L R hcomm)))
      ((map_continuous (MaxTensor.lift L R hcomm)).mul continuous_const)
  | ih x =>
    change Commute c (MaxTensor.lift L R hcomm (MaxTensor.of x))
    suffices ∀ tensor : A ⊗[ℂ] D,
        Commute c (MaxTensor.lift L R hcomm (MaxTensor.of (MaxTensor.rawEquiv tensor))) from
      this (MaxTensor.rawEquiv.symm x)
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | tmul a d =>
      change Commute c (MaxTensor.lift L R hcomm (MaxTensor.of (a ⊗ₜ[ℂ] d)))
      rw [MaxTensor.lift_of_tmul]
      exact (hL a).mul_right (hR d)
    | add x y hx hy => simpa only [map_add] using hx.add_right hy
end KirchbergRordam
namespace KirchbergRordam
section
open Filter Topology NormUltrapower


theorem maximal_absorption_of_central_half_flip
    (A D : Type*) [CStarAlgebra A] [CStarAlgebra D]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
    (ω : Ultrafilter ℕ) (ι : D →⋆ₐ[ℂ] CentralAlgebra A ω)
    (u : ℕ → unitary (MaxTensor.Algebra D D))
    (hu : ∀ d, Tendsto (fun n => Unitary.conjStarAlgAut ℂ _ (u n)
      (MaxTensor.includeLeft d)) atTop (𝓝 (MaxTensor.includeRight d))) :
    Nonempty (A ≃⋆ₐ[ℂ] MaxTensor.Algebra A D) := by
  classical
  let B := MaxTensor.Algebra A D
  let : TopologicalSpace.SeparableSpace B := MaxTensor.separable_maxTensor
  let φ : A →⋆ₐ[ℂ] B := MaxTensor.includeLeft
  let r : D →⋆ₐ[ℂ] B := MaxTensor.includeRight
  let ι₀ : D →⋆ₐ[ℂ] NormUltrapower.Algebra A ω := (centralSubalgebra ω).subtype.comp ι
  have hc (a : A) (d : D) : Commute (NormUltrapower.diagonal ω a) (ι₀ d) :=
    (mem_central_iff ω (ι d : NormUltrapower.Algebra A ω)).mp (ι d).property a
  let ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω := MaxTensor.lift (NormUltrapower.diagonal ω) ι₀ hc
  have hs (a : A) : ψ (φ a)=NormUltrapower.diagonal ω a :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft (NormUltrapower.diagonal ω) ι₀ hc) a
  have hsR (d : D) : ψ (r d)=ι₀ d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight (NormUltrapower.diagonal ω) ι₀ hc) d
  have hφ : Function.Injective φ := by
    intro a b hab
    apply (diagonal_isometry ω).injective
    rw [← hs a,← hs b,hab]
  let L : D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := (NormUltrapower.map φ ω).comp ι₀
  let R : D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := (NormUltrapower.diagonal ω).comp r
  have hLR (d e : D) : Commute (L d) (R e) := ultrapower_left_commutes_right ω (ι₀ d) e
  let U : MaxTensor.Algebra D D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := MaxTensor.lift L R hLR
  have hUL (d : D) : U (MaxTensor.includeLeft d)=L d :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft L R hLR) d
  have hUR (d : D) : U (MaxTensor.includeRight d)=R d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight L R hLR) d
  let v : ℕ → unitary (NormUltrapower.Algebra B ω) := fun n => ⟨U (u n),Unitary.map_mem U (u n).property⟩
  have hUa (a : A) (x : MaxTensor.Algebra D D) : Commute (NormUltrapower.diagonal ω (φ a)) (U x) := by
    apply maximal_lift_image_commutes L R hLR
    · intro d
      have he := congrArg (NormUltrapower.map φ ω) (hc a d).eq
      change NormUltrapower.diagonal ω (φ a)*NormUltrapower.map φ ω (ι₀ d) =
        NormUltrapower.map φ ω (ι₀ d)*NormUltrapower.diagonal ω (φ a)
      simpa only [map_mul,map_diagonal] using he
    · intro d
      exact (MaxTensor.legs_commute a d).map (NormUltrapower.diagonal ω)
  let F : ℕ → B →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := fun n =>
    (Unitary.conjStarAlgAut ℂ _ (v n)).toStarAlgHom.comp ((NormUltrapower.map φ ω).comp ψ)
  have hFL (a : A) : Tendsto (fun n => F n (φ a)) atTop (𝓝 (NormUltrapower.diagonal ω (φ a))) := by
    have he (n : ℕ) : F n (φ a)=NormUltrapower.diagonal ω (φ a) := by
      change Unitary.conjStarAlgAut ℂ _ (v n) (NormUltrapower.map φ ω (ψ (φ a)))=_
      rw [hs,map_diagonal,Unitary.conjStarAlgAut_apply]
      change U (u n)*NormUltrapower.diagonal ω (φ a)*star (U (u n))=NormUltrapower.diagonal ω (φ a)
      rw [← (hUa a (u n)).eq,mul_assoc]
      have hv : U (u n)*star (U (u n))=1 := (v n).property.2
      rw [hv,mul_one]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => NormUltrapower.diagonal ω (φ a)) atTop (𝓝 (NormUltrapower.diagonal ω (φ a))))
  have hFR (d : D) : Tendsto (fun n => F n (r d)) atTop (𝓝 (NormUltrapower.diagonal ω (r d))) := by
    have he (n : ℕ) : F n (r d)=U (Unitary.conjStarAlgAut ℂ _ (u n) (MaxTensor.includeLeft d)) := by
      change Unitary.conjStarAlgAut ℂ _ (v n) (NormUltrapower.map φ ω (ψ (r d)))=_
      rw [hsR]
      simp only [Unitary.conjStarAlgAut_apply,map_mul,map_star,hUL]
      rfl
    have hU : LipschitzWith 1 U := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one,one_mul]
      rw [dist_eq_norm,← map_sub,dist_eq_norm]
      exact NonUnitalStarAlgHom.norm_apply_le U (x-y)
    have ht := (hU.continuous.tendsto (MaxTensor.includeRight d)).comp (hu d)
    rw [hUR] at ht
    change Tendsto (fun n => U (Unitary.conjStarAlgAut ℂ _ (u n) (MaxTensor.includeLeft d)))
      atTop (𝓝 (NormUltrapower.diagonal ω (r d))) at ht
    exact ht.congr (fun n => (he n).symm)
  have hF := MaxTensor.pointwise_limit_of_tensor_legs F (NormUltrapower.diagonal ω) hFL hFR
  apply isomorphism_of_ultrapower_split_and_conjugacy ω φ hφ ψ hs
  intro T ε hε
  have htest (b : B) (_ : b ∈ T) : ∀ᶠ n in atTop, dist (F n b) (NormUltrapower.diagonal ω b)<ε :=
    (hF b).eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨n,hn⟩ := (T.eventually_all.mpr htest).exists
  exact ⟨v n,hn⟩



theorem inner_local_of_ultrapower_split_and_conjugacy
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B)
    (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
    (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
    (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
        dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
          (NormUltrapower.diagonal ω b) < ε)
    (S : Finset A) (T : Finset B) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary B,
      (∀ a ∈ S, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) (φ a) < ε) ∧
      (∀ b ∈ T, ∃ a : A, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) b < ε) := by
  classical
  obtain ⟨u,hu⟩ := hconj (T ∪ S.image φ) ε hε
  obtain ⟨v,hv⟩ := unitary_lift ω u
  let w : ℕ → unitary B := fun n => ⟨(v : BoundedSeq B) n,
    ⟨congrArg (fun f : BoundedSeq B => f n) v.property.1,
      congrArg (fun f : BoundedSeq B => f n) v.property.2⟩⟩
  let β : ℕ → B ≃⋆ₐ[ℂ] B := fun n => Unitary.conjStarAlgAut ℂ B (w n)
  let x : B → BoundedSeq A := fun b => (Ideal.Quotient.mk_surjective (ψ b)).choose
  have hx (b : B) : quotientMap ω (x b) = ψ b :=
    (Ideal.Quotient.mk_surjective (ψ b)).choose_spec
  have hfix (a : A) (ha : a ∈ S) :
      ∀ᶠ n in (ω : Filter ℕ), dist (β n (φ a)) (φ a) < ε := by
    have h := hu (φ a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
    rw [hsplit,map_diagonal] at h
    let z : BoundedSeq B := (v : BoundedSeq B)*constantSeq (φ a)*star (v : BoundedSeq B)-constantSeq (φ a)
    have hz : ‖quotientMap ω z‖ < ε := by
      simpa only [z,map_sub,map_mul,map_star,hv,NormUltrapower.diagonal,StarAlgHom.comp_apply,dist_eq_norm,
        Unitary.conjStarAlgAut_apply,Unitary.coe_star] using h
    simp only [dist_eq_norm]
    exact eventually_norm_lt ω z ε hz
  have hdense (b : B) (hb : b ∈ T) :
      ∀ᶠ n in (ω : Filter ℕ), dist (β n (φ (x b n))) b < ε := by
    have h := hu b (Finset.mem_union_left _ hb)
    let z : BoundedSeq B := (v : BoundedSeq B)*sequenceMap φ (x b)*star (v : BoundedSeq B)-constantSeq b
    have hmap : quotientMap ω (sequenceMap φ (x b))=NormUltrapower.map φ ω (ψ b) := by
      rw [← map_mk,hx]
    have hz : ‖quotientMap ω z‖ < ε := by
      simpa only [z,map_sub,map_mul,map_star,hv,hmap,NormUltrapower.diagonal,StarAlgHom.comp_apply,dist_eq_norm,
        Unitary.conjStarAlgAut_apply,Unitary.coe_star] using h
    simp only [dist_eq_norm]
    exact eventually_norm_lt ω z ε hz
  have hallS : ∀ᶠ n in (ω : Filter ℕ), ∀ a ∈ S, dist (β n (φ a)) (φ a) < ε :=
    S.eventually_all.mpr hfix
  have hallT : ∀ᶠ n in (ω : Filter ℕ), ∀ b ∈ T, dist (β n (φ (x b n))) b < ε :=
    T.eventually_all.mpr hdense
  obtain ⟨n,hnS,hnT⟩ := (hallS.and hallT).exists
  exact ⟨w n,hnS,fun b hb => ⟨x b n,hnT b hb⟩⟩
end

open Filter Topology


theorem local_approximate_surjectivity_of_dense_quotient
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace C]
    (φ : A →⋆ₐ[ℂ] B) (q : B →⋆ₐ[ℂ] C) (hq : DenseRange q)
    (hinj : Function.Injective (q.comp φ))
    (hlocal : ∀ (S : Finset A) (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary B,
        (∀ a ∈ S, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) (φ a) < ε) ∧
        (∀ b ∈ T, ∃ a : A, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) b < ε)) :
    Nonempty (A ≃⋆ₐ[ℂ] C) := by
  classical
  have hqdist (x y : B) : dist (q x) (q y) ≤ dist x y := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le q (x-y)
  apply local_approximate_surjectivity (q.comp φ) hinj
  intro S T ε hε
  have he : 0 < ε/2 := half_pos hε
  choose b hb using fun t : C => hq.exists_dist_lt t he
  obtain ⟨u,hfix,happrox⟩ := hlocal S (T.image b) (ε/2) he
  let v : unitary C := ⟨q u, Unitary.map_mem q u.property⟩
  have hconj (x : B) :
      Unitary.conjStarAlgAut ℂ C v (q x) = q (Unitary.conjStarAlgAut ℂ B u x) := by
    simp only [Unitary.conjStarAlgAut_apply, map_mul, map_star]
    rfl
  refine ⟨Unitary.conjStarAlgAut ℂ C v, ?_, ?_⟩
  · intro a ha
    change dist (Unitary.conjStarAlgAut ℂ C v (q (φ a))) (q (φ a)) < ε
    rw [hconj]
    exact (hqdist _ _).trans_lt ((hfix a ha).trans (half_lt_self hε))
  · intro t ht
    obtain ⟨a,ha⟩ := happrox (b t) (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
    refine ⟨a,?_⟩
    change dist (Unitary.conjStarAlgAut ℂ C v (q (φ a))) t < ε
    rw [hconj]
    have h1 := (hqdist (Unitary.conjStarAlgAut ℂ B u (φ a)) (b t)).trans_lt ha
    have h2 := hb t
    have htri := dist_triangle (q (Unitary.conjStarAlgAut ℂ B u (φ a))) (q (b t)) t
    rw [dist_comm (q (b t)) t] at htri
    linarith


theorem quotient_isomorphism_of_ultrapower_split_and_conjugacy
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace C]
    (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B)
    (q : B →⋆ₐ[ℂ] C) (hq : DenseRange q)
    (hinj : Function.Injective (q.comp φ))
    (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
    (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
    (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
        dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
          (NormUltrapower.diagonal ω b) < ε) :
    Nonempty (A ≃⋆ₐ[ℂ] C) :=
  local_approximate_surjectivity_of_dense_quotient φ q hq hinj
    (inner_local_of_ultrapower_split_and_conjugacy ω φ ψ hsplit hconj)
end KirchbergRordam

end

end OAI
