import OAI.Analysis.CharacterCriterion.SeparableReduction

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


namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma exists_bounded_representative (ω : Ultrafilter ℕ) (x : Algebra A ω)
    {c : ℝ} (hc : ‖x‖ < c) :
    ∃ v : BoundedSeq A, quotientMap ω v = x ∧ ‖v‖ ≤ c := by
  obtain ⟨v,hv⟩ := Ideal.Quotient.mk_surjective x
  have hp : 0 ≤ c := (norm_nonneg x).trans hc.le
  refine ⟨cutRepresentative v c hp, ?_, cutRepresentative_norm_le v c hp⟩
  have hn : normLimit ω v < c := by rw [← norm_mk_eq, hv]; exact hc
  exact (cutRepresentative_mk_eq ω v c hp hn).symm.trans hv

inductive CollapseTest (S : Type*)
  | add (x y : S) | mul (x y : S) | adjoint (x : S)
  | zero | one | imag | value (x : S)
  deriving Countable

namespace CollapseTest
variable {S : Type*} [Ring S] [StarRing S]

def eval {B : Type*} [CStarAlgebra B] (j : S) (f : S → B) : CollapseTest S → B
  | .add x y => f (x+y)-(f x+f y)
  | .mul x y => f (x*y)-f x*f y
  | .adjoint x => f (star x)-star (f x)
  | .zero => f 0
  | .one => f 1-1
  | .imag => f j-algebraMap ℂ B Complex.I
  | .value x => f x

lemma natural {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (j : S) (f : S → B) (ψ : B →⋆ₐ[ℂ] C) (i : CollapseTest S) :
    ψ (eval j f i) = eval j (fun x => ψ (f x)) i := by
  cases i <;> simp only [eval,map_add,map_mul,map_sub,map_one,map_star]
  exact congrArg (fun z => ψ (f j)-z) (ψ.commutes Complex.I)

lemma apply_seq {B : Type*} [CStarAlgebra B] (j : S) (f : S → BoundedSeq B)
    (i : CollapseTest S) (n : ℕ) :
    eval j f i n = eval j (fun x => f x n) i := by
  cases i <;> rfl
end CollapseTest


theorem countable_iterated_collapse {S : Type*} [Ring S] [StarRing S] [Countable S]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : S →+* Algebra (CentralAlgebra A ω) ω)
    (hφ : ∀ x, φ (star x) = star (φ x))
    (j : S) (hj : φ j = algebraMap ℂ (Algebra (CentralAlgebra A ω) ω) Complex.I) :
    ∃ θ : S →+* CentralAlgebra A ω,
      (∀ x, θ (star x) = star (θ x)) ∧
      (∀ x, ‖θ x‖ = ‖φ x‖) ∧
      θ j = algebraMap ℂ (CentralAlgebra A ω) Complex.I := by
  classical
  let F := CentralAlgebra A ω
  have hex (x : S) : ∃ u : BoundedSeq F, quotientMap ω u = φ x := Ideal.Quotient.mk_surjective _
  choose u hu using hex
  have hexi (x : S) (s : ℕ) : ∃ v : BoundedSeq A,
      quotientMap ω v = (u x s : Algebra A ω) ∧ ‖v‖ ≤ ‖u x‖+1 :=
    exists_bounded_representative ω _ ((u x).norm_coe_le_norm s |>.trans_lt (lt_add_one _))
  choose v hv hvnorm using hexi
  let a : ℕ → A := denseSeq A
  have ha : DenseRange a := denseRange_denseSeq A
  let test : (CollapseTest S ⊕ (S×ℕ)) → ℕ → ℕ → ℝ
    | .inl i, s, l => ‖CollapseTest.eval j (fun x => v x s) i l‖-
        ‖CollapseTest.eval j (fun x => u x s) i‖
    | .inr (x,n), s, l => ‖v x s l*a n-a n*v x s l‖
  have htcore (i : CollapseTest S) (s : ℕ) :
      Tendsto (test (.inl i) s) (ω : Filter ℕ) (𝓝 0) := by
    let z := CollapseTest.eval j (fun x => v x s) i
    have hz : quotientMap ω z =
        ((centralSubalgebra ω).subtype (CollapseTest.eval j (fun x => u x s) i)) := by
      rw [CollapseTest.natural,CollapseTest.natural]
      simp only [hv]
      rfl
    have hzNorm : normLimit ω z = ‖CollapseTest.eval j (fun x => u x s) i‖ := by
      rw [← norm_mk_eq]
      change ‖quotientMap ω z‖ = _
      rw [hz]
      rfl
    simpa only [test,hzNorm,sub_self] using
      (tendsto_norm ω z).sub_const ‖CollapseTest.eval j (fun x => u x s) i‖
  have ht (i : CollapseTest S ⊕ (S×ℕ)) (s : ℕ) :
      Tendsto (test i s) (ω : Filter ℕ) (𝓝 0) := by
    rcases i with i | ⟨x,n⟩
    · exact htcore i s
    · exact (mk_mem_central_iff ω (v x s)).mp (by rw [hv]; exact (u x s).property) (a n)
  obtain ⟨k,hk⟩ := Reindex.diagonal_select (ω : Filter ℕ) test ht
  have hfree : (ω : Filter ℕ) ≤ atTop := by simpa only [Nat.cofinite_eq_atTop] using hω
  have hk' (i) : Tendsto (fun s => test i s (k s)) (ω : Filter ℕ) (𝓝 0) :=
    (hk i).mono_left hfree
  let w : S → BoundedSeq A := fun x =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun s => v x s (k s)) (‖u x‖+1)
      (fun s => ((v x s).norm_coe_le_norm _).trans (hvnorm x s))
  let g : S → Algebra A ω := fun x => quotientMap ω (w x)
  have hgtest (i : CollapseTest S) : ‖CollapseTest.eval j g i‖ = ‖CollapseTest.eval j φ i‖ := by
    have hout : Tendsto (fun s => ‖CollapseTest.eval j (fun x => u x s) i‖)
        (ω : Filter ℕ) (𝓝 ‖CollapseTest.eval j φ i‖) := by
      have hz : quotientMap ω (CollapseTest.eval j u i) = CollapseTest.eval j φ i := by
        rw [CollapseTest.natural]
        simp only [hu]
      have hn : normLimit ω (CollapseTest.eval j u i) = ‖CollapseTest.eval j φ i‖ := by
        rw [← norm_mk_eq]
        exact congrArg norm hz
      simpa only [CollapseTest.apply_seq,hn] using tendsto_norm ω (CollapseTest.eval j u i)
    have htend : Tendsto (fun s => ‖CollapseTest.eval j w i s‖)
        (ω : Filter ℕ) (𝓝 ‖CollapseTest.eval j φ i‖) := by
      have h := (hk' (.inl i)).add hout
      simp only [zero_add] at h
      apply h.congr
      intro s
      simp only [test,sub_add_cancel,CollapseTest.apply_seq]
      rfl
    have hn : ‖CollapseTest.eval j g i‖ = normLimit ω (CollapseTest.eval j w i) := by
      rw [← CollapseTest.natural j w (quotientMap ω) i]
      exact norm_mk_eq ω _
    rw [hn]
    exact tendsto_nhds_unique (tendsto_norm ω _) htend
  have hadd (x y : S) : g (x+y)=g x+g y := by
    have h := hgtest (.add x y)
    simp only [CollapseTest.eval,map_add,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] at h
    exact h
  have hmul (x y : S) : g (x*y)=g x*g y := by
    have h := hgtest (.mul x y)
    simp only [CollapseTest.eval,map_mul,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] at h
    exact h
  have hstar (x : S) : g (star x)=star (g x) := by
    have h := hgtest (.adjoint x)
    simp only [CollapseTest.eval,hφ,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] at h
    exact h
  have hzero : g 0=0 := by
    have h := hgtest .zero
    simpa only [CollapseTest.eval,map_zero,norm_zero,norm_eq_zero] using h
  have hone : g 1=1 := by
    have h := hgtest .one
    simpa only [CollapseTest.eval,map_one,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using h
  have hI : g j=algebraMap ℂ (Algebra A ω) Complex.I := by
    have h := hgtest .imag
    simpa only [CollapseTest.eval,hj,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using h
  have hgCentral (x : S) : g x ∈ centralSubalgebra ω := by
    rw [mem_central_iff]
    intro c
    refine ha.induction_on c (p:=fun c => diagonal ω c*g x=g x*diagonal ω c)
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro n
    have he := (quotient_eq_iff ω (w x*constantSeq (a n)) (constantSeq (a n)*w x)).mpr
      (hk' (.inr (x,n)))
    change quotientMap ω (constantSeq (a n))*quotientMap ω (w x)=
      quotientMap ω (w x)*quotientMap ω (constantSeq (a n))
    simpa only [map_mul] using he.symm
  let θ : S →+* CentralAlgebra A ω :=
    { toFun := fun x => ⟨g x,hgCentral x⟩
      map_zero' := Subtype.ext hzero
      map_one' := Subtype.ext hone
      map_add' := fun x y => Subtype.ext (hadd x y)
      map_mul' := fun x y => Subtype.ext (hmul x y) }
  exact ⟨θ,fun x => Subtype.ext (hstar x),fun x => hgtest (.value x),Subtype.ext hI⟩
end KirchbergRordam.NormUltrapower

namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra


theorem iterated_central_collapse {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
    [SeparableSpace A] [SeparableSpace D]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : D →⋆ₐ[ℂ] Algebra (CentralAlgebra A ω) ω) :
    ∃ θ : D →⋆ₐ[ℂ] CentralAlgebra A ω, ∀ x, ‖θ x‖ = ‖φ x‖ := by
  classical
  let : _root_.Algebra ℚ D := Algebra.compHom D (algebraMap ℚ ℂ)
  obtain ⟨S,hcount,hden,hI⟩ := RationalDense.exists_countable_dense_star (A:=D)
  let : Countable S := hcount.to_subtype
  let f : S →+* Algebra (CentralAlgebra A ω) ω := φ.toRingHom.comp S.subtype.toRingHom
  have hfstar (x : S) : f (star x)=star (f x) := map_star φ (x:D)
  have hfI : f ⟨_,hI⟩=algebraMap ℂ (Algebra (CentralAlgebra A ω) ω) Complex.I := φ.commutes _
  obtain ⟨g,hgs,hgn,hgi⟩ := countable_iterated_collapse ω hω f hfstar ⟨_,hI⟩ hfI
  have hbound (x : S) : ‖g x‖ ≤ ‖x‖ := by
    rw [hgn]
    exact NonUnitalStarAlgHom.norm_apply_le φ (x:D)
  have hLip : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub]
    exact hbound (x-y)
  obtain ⟨θ,hθ⟩ := RationalDense.extend_complex S hden g hLip.uniformContinuous hgs hI hgi
  refine ⟨θ,fun x => ?_⟩
  refine hden.denseRange_val.induction_on x
    (p:=fun x => ‖θ x‖=‖φ x‖)
    (isClosed_eq (continuous_norm.comp (map_continuous θ)) (continuous_norm.comp (map_continuous φ))) ?_
  intro x
  rw [hθ]
  exact hgn x
end KirchbergRordam.NormUltrapower

end

end OAI
