import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerUnitaryLift
import OAI.Analysis.JiangSu.CStarAlgebras.IsometricHomLimit

namespace OAI

noncomputable section


namespace CStarIntertwining
open Filter Topology
open scoped CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def error (n : ℕ) : ℝ := (1/2)^n
lemma error_pos (n : ℕ) : 0<error n := pow_pos (by norm_num) _
lemma error_tendsto : Tendsto error atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma error_add (n m : ℕ) : error (n+m)=error n*error m := pow_add _ _ _

lemma controlled_cauchy (φ : ℕ → A →⋆ₐ[ℂ] B) (S : ℕ → Finset A) (hS : Monotone S)
    (hstep : ∀ n x,x∈S n → dist (φ n x) (φ (n+1) x)≤error n)
    {N : ℕ} {x : A} (hx : x∈S N) : CauchySeq (fun n => φ n x) := by
  apply (cauchySeq_shift N).mp
  apply cauchySeq_of_le_geometric (1/2:ℝ) (error N) (by norm_num)
  intro k
  have hh := hstep (k+N) x (hS (Nat.le_add_left N k) hx)
  simpa only [Nat.add_right_comm k 1 N, error, pow_add, mul_comm] using hh

lemma controlled_limit_distance (φ : ℕ → A →⋆ₐ[ℂ] B) (S : ℕ → Finset A) (hS : Monotone S)
    (hstep : ∀ n x,x∈S n → dist (φ n x) (φ (n+1) x)≤error n)
    (ψ : A →⋆ₐ[ℂ] B) (hψ : ∀ x,Tendsto (fun n => φ n x) atTop (𝓝 (ψ x)))
    {N : ℕ} {x : A} (hx : x∈S N) : dist (φ N x) (ψ x)≤2*error N := by
  have hs (k : ℕ) : dist (φ (k+N) x) (φ ((k+1)+N) x)≤error N*(1/2:ℝ)^k := by
    have hh := hstep (k+N) x (hS (Nat.le_add_left N k) hx)
    simpa only [Nat.add_right_comm k 1 N, error, pow_add, mul_comm] using hh
  have ht : Tendsto (fun k => φ (k+N) x) atTop (𝓝 (ψ x)) :=
    (hψ x).comp (tendsto_add_atTop_nat N)
  have h := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) (error N) (by norm_num) hs ht
  norm_num only [Nat.zero_add,show 1-(1/2:ℝ)=1/2 by norm_num] at h
  convert h using 1
  ring

 theorem equiv_of_chain (φ : ℕ → A →⋆ₐ[ℂ] B) (hφ : ∀ n,Isometry (φ n))
    (S : ℕ → Finset A) (hS : Monotone S)
    (a : ℕ → A) (ha : DenseRange a) (b : ℕ → B) (hb : DenseRange b)
    (hamem : ∀ j,a j∈S j)
    (hstep : ∀ n x,x∈S n → dist (φ n x) (φ (n+1) x)≤error n)
    (hpreimage : ∀ n j,j≤n → ∃ x∈S (n+1),dist (φ (n+1) x) (b j)≤error n) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  obtain ⟨ψ,hψ⟩ := exists_limit_hom φ a ha (fun j => controlled_cauchy φ S hS hstep (hamem j))
  have hi : Isometry ψ := limit_hom_isometry φ hφ ψ hψ
  have hc : IsClosed (Set.range ψ) := hi.isClosedEmbedding.isClosed_range
  have hbm (j : ℕ) : b j∈Set.range ψ := by
    rw [←hc.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have ht : Tendsto (fun n => 3*error n) atTop (𝓝 0) := by
      simpa using error_tendsto.const_mul 3
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
    let n := max N j
    obtain ⟨x,hx,hxb⟩ := hpreimage n j (le_max_right N j)
    refine ⟨ψ x,⟨x,rfl⟩,?_⟩
    have hlim := controlled_limit_distance φ S hS hstep ψ hψ hx
    have he : error (n+1)=error n/2 := by simp [error,pow_succ]; ring
    have hbnd := dist_triangle (b j) (φ (n+1) x) (ψ x)
    rw [dist_comm (b j) (φ (n+1) x)] at hbnd
    have hn := hN n (le_max_left N j)
    have hp := error_pos n
    rw [he] at hlim
    linarith
  have hd : DenseRange ψ := hb.mono (by rintro _ ⟨j,rfl⟩; exact hbm j)
  have hsur : Function.Surjective ψ := by
    intro y
    have hh := hd y
    rwa [hc.closure_eq] at hh
  exact ⟨StarAlgEquiv.ofBijective ψ ⟨hi.injective,hsur⟩⟩

end CStarIntertwining


namespace CStarIntertwining
open scoped CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def LocalApproximation (ι : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ (F : Finset A) (G : Finset B) (ε : ℝ),0<ε →
    ∃ β : B ≃⋆ₐ[ℂ] B,
      (∀ x∈F,dist (β (ι x)) (ι x)<ε) ∧
      ∀ y∈G,∃ x : A,dist (β (ι x)) y<ε

structure ProtectedEmbedding (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] where
  automorphism : B ≃⋆ₐ[ℂ] B
  tracked : Finset A

def ProtectedEmbedding.hom (ι : A →⋆ₐ[ℂ] B) (P : ProtectedEmbedding A B) : A →⋆ₐ[ℂ] B :=
  P.automorphism.toStarAlgHom.comp ι

def Transition (ι : A →⋆ₐ[ℂ] B) (a : ℕ → A) (b : ℕ → B) (n : ℕ)
    (P Q : ProtectedEmbedding A B) : Prop :=
  P.tracked⊆Q.tracked ∧ a (n+1)∈Q.tracked ∧
  (∀ x∈P.tracked,dist (P.hom ι x) (Q.hom ι x)≤error n) ∧
  ∀ j≤n,∃ x∈Q.tracked,dist (Q.hom ι x) (b j)≤error n

lemma transition_exists (ι : A →⋆ₐ[ℂ] B) (h : LocalApproximation ι)
    (a : ℕ → A) (b : ℕ → B) (n : ℕ) (P : ProtectedEmbedding A B) :
    ∃ Q,Transition ι a b n P Q := by
  classical
  let G := (Finset.range (n+1)).image (fun j => P.automorphism.symm (b j))
  obtain ⟨β,hβ,hb⟩ := h P.tracked G (error n) (error_pos n)
  have hx (j : Fin (n+1)) : ∃ x : A,dist (β (ι x)) (P.automorphism.symm (b j))<error n :=
    hb _ (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr j.isLt,rfl⟩)
  choose x hx using hx
  let Q : ProtectedEmbedding A B := ⟨β.trans P.automorphism,
    P.tracked∪Finset.univ.image x∪{a (n+1)}⟩
  refine ⟨Q,?_,?_,?_,?_⟩
  · intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · intro x hxp
    change dist (P.automorphism (ι x)) (P.automorphism (β (ι x)))≤error n
    rw [(StarAlgEquiv.isometry P.automorphism).dist_eq,dist_comm]
    exact (hβ x hxp).le
  · intro j hj
    let k : Fin (n+1) := ⟨j,by omega⟩
    refine ⟨x k,Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)),?_⟩
    change dist (P.automorphism (β (ι (x k)))) (b j)≤error n
    rw [←P.automorphism.apply_symm_apply (b j),(StarAlgEquiv.isometry P.automorphism).dist_eq]
    exact (hx k).le

 theorem equiv_of_local_approximation [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] (ι : A →⋆ₐ[ℂ] B) (hi : Isometry ι)
    (h : LocalApproximation ι) : Nonempty (A ≃⋆ₐ[ℂ] B) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨b,hb⟩ := TopologicalSpace.exists_dense_seq B
  let next (n : ℕ) (P : ProtectedEmbedding A B) : ProtectedEmbedding A B :=
    (transition_exists ι h a b n P).choose
  have hnext (n : ℕ) (P : ProtectedEmbedding A B) : Transition ι a b n P (next n P) :=
    (transition_exists ι h a b n P).choose_spec
  let P : ℕ → ProtectedEmbedding A B := Nat.rec ⟨StarAlgEquiv.refl ℂ B, {a 0}⟩ next
  have hP (n : ℕ) : Transition ι a b n (P n) (P (n+1)) := hnext n (P n)
  have hS : Monotone (fun n => (P n).tracked) := monotone_nat_of_le_succ (fun n => (hP n).1)
  have hamem (j : ℕ) : a j∈(P j).tracked := by
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j => exact (hP j).2.1
  apply equiv_of_chain (fun n => (P n).hom ι)
    (fun n => (StarAlgEquiv.isometry (P n).automorphism).comp hi) (fun n => (P n).tracked) hS a ha b hb hamem
  · intro n x hx
    exact (hP n).2.2.1 x hx
  · intro n j hj
    exact (hP n).2.2.2 j hj

end CStarIntertwining


namespace CStarIntertwining
open Filter Topology DirectComparison NormUltra NormUltra.QuotientAlgebra
open scoped CStarAlgebra ENNReal

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [PartialOrder B] [StarOrderedRing B]

 def diagonal (U : Ultrafilter ℕ) (b : B) : QuotientAlgebra (fun _ : ℕ => B) U :=
  mk U (boundedDiagonal b)

 omit [PartialOrder B] [StarOrderedRing B] in
 lemma eventually_norm_lt (U : Ultrafilter ℕ) (x : BoundedFamilies (fun _ : ℕ => B))
    {ε : ℝ} (h : ‖mk U x‖<ε) : ∀ᶠ n in (U : Filter ℕ),‖x n‖<ε := by
  rw [norm_mk_eq_limsup] at h
  exact eventually_lt_of_limsup_lt h (BoundedFamilies.norm_bounded U x)

 def QuotientConjugacy (U : Ultrafilter ℕ) (ι : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ (F : Finset A) (G : Finset B) (ε : ℝ),0<ε →
    ∃ u : unitary (QuotientAlgebra (fun _ : ℕ => B) U),
      (∀ x∈F,‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*diagonal U (ι x)*star u-diagonal U (ι x)‖<ε) ∧
      ∀ y∈G,∃ x : QuotientAlgebra (fun _ : ℕ => A) U,
        ‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*QuotientAlgebra.map U ι x*star u-diagonal U y‖<ε

 omit [PartialOrder B] [StarOrderedRing B] in
 theorem local_approximation_of_quotient (U : Ultrafilter ℕ) (ι : A →⋆ₐ[ℂ] B)
    (h : QuotientConjugacy U ι) : LocalApproximation ι := by
  classical
  intro F G ε hε
  obtain ⟨u,hu,hG⟩ := h F G ε hε
  obtain ⟨v,hv⟩ := unitary_representative U u
  have htransfer (a : BoundedFamilies (fun _ : ℕ => A)) (b : B)
      (hh : ‖(u : QuotientAlgebra (fun _ : ℕ => B) U)*mk U (boundedMap ι a)*star u-diagonal U b‖<ε) :
      ∀ᶠ n in (U : Filter ℕ),‖(v n : B)*ι (a n)*star (v n : B)-b‖<ε := by
    let z := boundedUnitary v*boundedMap ι a*star (boundedUnitary v)-boundedDiagonal b
    have hz : ‖mk U z‖<ε := by
      simpa only [z,mk_sub,mk_mul,mk_star,hv,diagonal,Unitary.coe_star] using hh
    exact eventually_norm_lt U z hz
  have hf : ∀ᶠ n in (U : Filter ℕ),∀ x∈F,‖(v n : B)*ι x*star (v n : B)-ι x‖<ε := by
    apply (Filter.eventually_all_finset F).mpr
    intro x hx
    apply htransfer (boundedDiagonal x) (ι x)
    simpa only [boundedMap_diagonal,diagonal] using hu x hx
  have hg (y : G) : ∃ x : BoundedFamilies (fun _ : ℕ => A),
      ∀ᶠ n in (U : Filter ℕ),‖(v n : B)*ι (x n)*star (v n : B)-(y:B)‖<ε := by
    obtain ⟨x,hx⟩ := hG y y.2
    obtain ⟨a,rfl⟩ := mk_surjective x
    exact ⟨a,htransfer a y hx⟩
  choose x hx using hg
  have hg' : ∀ᶠ n in (U : Filter ℕ),∀ y : G,‖(v n : B)*ι (x y n)*star (v n : B)-(y:B)‖<ε :=
    Filter.eventually_all.mpr hx
  obtain ⟨n,hfn,hgn⟩ := (hf.and hg').exists
  refine ⟨Unitary.conjStarAlgAut ℂ B (v n),?_,?_⟩
  · intro x hx
    simpa only [Unitary.conjStarAlgAut_apply,dist_eq_norm] using hfn x hx
  · intro y hy
    refine ⟨x ⟨y,hy⟩ n,?_⟩
    simpa only [Unitary.conjStarAlgAut_apply,dist_eq_norm] using hgn ⟨y,hy⟩

 omit [PartialOrder B] [StarOrderedRing B] in
 theorem equiv_of_quotient_conjugacy [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] (U : Ultrafilter ℕ) (ι : A →⋆ₐ[ℂ] B) (hi : Isometry ι)
    (h : QuotientConjugacy U ι) : Nonempty (A ≃⋆ₐ[ℂ] B) :=
  equiv_of_local_approximation ι hi (local_approximation_of_quotient U ι h)

end CStarIntertwining

end

end OAI
