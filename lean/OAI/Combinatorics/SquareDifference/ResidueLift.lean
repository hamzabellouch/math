import OAI.Combinatorics.SquareDifference.FourierLift

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

def IsSquareDifferenceFree (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a-b ≠ (m : ℤ)^2

noncomputable def squareStepChild (A : Finset ℤ) (L D : ℕ) (c : ℤ) : Finset ℤ :=
  (Icc 1 (L : ℤ)).filter (fun n => (D : ℤ)^2*n+c∈A)

lemma squareStepChild_subset (A : Finset ℤ) (L D : ℕ) (c : ℤ) :
    squareStepChild A L D c⊆Icc 1 (L : ℤ) := filter_subset _ _

lemma squareStepChild_free (A : Finset ℤ) (hA : IsSquareDifferenceFree A)
    (L D : ℕ) (hD : 1≤D) (c : ℤ) : IsSquareDifferenceFree (squareStepChild A L D c) := by
  intro a ha b hb m hm he
  have h := hA _ (mem_filter.mp ha).2 _ (mem_filter.mp hb).2 (D*m) (by nlinarith)
  apply h
  push_cast
  calc
    (D : ℤ)^2*a+c-((D : ℤ)^2*b+c)=(D : ℤ)^2*(a-b) := by ring
    _ = _ := by rw [he]; ring

lemma squareStepChild_mem (A : Finset ℤ) (L D : ℕ) (c n : ℤ) :
    n∈squareStepChild A L D c ↔ 1≤n ∧ n≤L ∧ (D : ℤ)^2*n+c∈A := by
  simp only [squareStepChild,mem_filter,mem_Icc,and_assoc]

lemma sum_range_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (D L : ℕ) (hD : 0<D) :
    (∑n∈range (D*L), f n)=∑j∈range D, ∑t∈range L, f (j+D*t) := by
  classical
  rw [← sum_product' (range D) (range L) (fun j t => f (j+D*t))]
  symm
  apply sum_bij (fun x _ => x.1+D*x.2)
  · intro x hx
    obtain ⟨hj,ht⟩ := mem_product.mp hx
    simp only [mem_range] at hj ht ⊢
    nlinarith
  · intro x hx y hy he
    obtain ⟨hxj,hxt⟩ := mem_product.mp hx
    obtain ⟨hyj,hyt⟩ := mem_product.mp hy
    have hj : x.1=y.1 := by
      have hh := congrArg (fun n => n%D) he
      simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (mem_range.mp hxj),
        Nat.mod_eq_of_lt (mem_range.mp hyj)] using hh
    have ht : x.2=y.2 := by rw [hj] at he; exact (Nat.mul_left_cancel hD (Nat.add_left_cancel he))
    exact Prod.ext hj ht
  · intro n hn
    refine ⟨(n%D,n/D), mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt n hD),mem_range.mpr ?_⟩,
      Nat.mod_add_div n D⟩
    apply (Nat.div_lt_iff_lt_mul hD).mpr
    simpa only [mul_comm] using mem_range.mp hn
  · intro x _; rfl

lemma squareStep_padded_sum {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    (N D L a : ℕ) (hD : 0<D) (ha : a<D) (hNL : N≤D^2*L)
    (hf : ∀n, N≤n → f n=0) :
    (∑n∈range N, if n%D=a then f n else 0)=
      ∑j∈range D, ∑t∈range L, f (a+D*j+D^2*t) := by
  classical
  have hpad : (∑n∈range N, if n%D=a then f n else 0)=
      ∑n∈range (D^2*L), if n%D=a then f n else 0 := by
    apply sum_subset (range_mono hNL)
    intro n hn hnN
    rw [hf n (by simpa only [mem_range,not_lt] using hnN)]
    split_ifs <;> rfl
  rw [hpad,show D^2*L=D*(D*L) by ring,sum_range_blocks _ D (D*L) hD]
  simp only [Nat.add_mul_mod_self_left]
  have hsel : (∑j∈range D, ∑t∈range (D*L), if j%D=a then f (j+D*t) else 0)=
      ∑t∈range (D*L), f (a+D*t) := by
    simp_rw [sum_ite_irrel,sum_const_zero]
    rw [sum_eq_single a]
    · rw [Nat.mod_eq_of_lt ha,ite_eq_left rfl]
    · intro j hj hja
      rw [Nat.mod_eq_of_lt (mem_range.mp hj),ite_eq_right hja]
    · intro h; exact (h (mem_range.mpr ha)).elim
  rw [hsel,sum_range_blocks _ D L hD]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro t _
  congr 1
  ring

lemma ceil_square_scale (N D : ℕ) (hN : 1≤N) (hD : 2≤D) :
    1≤N⌈/⌉D^2 ∧ N≤D^2*(N⌈/⌉D^2) ∧ (2≤N → N⌈/⌉D^2<N) := by
  have hD0 : 0<D^2 := by positivity
  have hpad : N≤D^2*(N⌈/⌉D^2) := (ceilDiv_le_iff_le_mul hD0).mp le_rfl
  refine ⟨?_,hpad,?_⟩
  · by_contra h
    have : N⌈/⌉D^2=0 := by omega
    simp only [this,mul_zero] at hpad
    omega
  · intro hN2
    have hceil : N⌈/⌉D^2≤N-1 := by
      apply (ceilDiv_le_iff_le_mul hD0).mpr
      have hNm : N-1+1=N := by omega
      nlinarith [sq_nonneg (D : ℤ)]
    omega

end SquareDifference

namespace SquareDifference

open Finset

section Fiber

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

omit [Fintype J] [DecidableEq J] [∀j,NeZero (p j)] in
lemma residueGate_plus_one (j : J) (x : ZMod (p j)) :
    residueGate (p j) x+1=if x=0 then (p j : ℝ) else 0 := by
  unfold residueGate
  split_ifs <;> ring

omit [∀j,NeZero (p j)] in
lemma sum_exactGate_powerset (B : Finset J) (z : ResidueSpace p) :
    (∑W∈B.powerset,exactGate p W z)=
      if ∀j∈B,z j=0 then (∏j∈B,p j : ℝ) else 0 := by
  classical
  have he : (∑W∈B.powerset,exactGate p W z)=∏j∈B,(residueGate (p j) (z j)+1) := by
    simpa only [exactGate,prod_const_one,mul_one] using
      (prod_add (fun j => residueGate (p j) (z j)) (fun _ => (1:ℝ)) B).symm
  rw [he]
  simp only [residueGate_plus_one]
  by_cases h : ∀j∈B,z j=0
  · rw [ite_eq_left h]
    exact prod_congr rfl (fun j hj => ite_eq_left (h j hj))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨j,hj,hz⟩ := h
    exact prod_eq_zero hj (ite_eq_right hz)

omit [Fintype J] [∀j,NeZero (p j)] in
lemma exactGate_union (U W : Finset J) (hUW : Disjoint U W) (z : ResidueSpace p) :
    exactGate p (U∪W) z=exactGate p U z*exactGate p W z := by
  exact prod_union hUW

lemma sum_exactGate_frozen {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (U B : Finset J) (hUB : Disjoint U B) (z x : ResidueSpace p) :
    (∑W∈B.powerset,exactGate p (U∪W) (coordinateFreeze p B z x))=
      exactGate p U x*(if ∀j∈B,z j=0 then (∏j∈B,p j : ℝ) else 0) := by
  have he (W : Finset J) (hW : W∈B.powerset) :
      exactGate p (U∪W) (coordinateFreeze p B z x)=exactGate p U x*exactGate p W z := by
    have hWB := mem_powerset.mp hW
    rw [exactGate_union p U W (hUB.mono_right hWB)]
    congr 1
    · apply prod_congr rfl
      intro j hj
      simp only [coordinateFreeze,ite_eq_right (disjoint_left.mp hUB hj)]
    · apply prod_congr rfl
      intro j hj
      simp only [coordinateFreeze,ite_eq_left (hWB hj)]
  rw [sum_congr rfl he,← mul_sum,sum_exactGate_powerset]

lemma liftPiece_frozen_complete (L : ℕ) (f : ℕ → ℝ) (U B : Finset J)
    (hUB : Disjoint U B) (z x : ResidueSpace p) :
    (∑W∈B.powerset,liftPiece p L f (U∪W) (coordinateFreeze p B z x))=
      ((∏j∈B,p j : ℝ)/(L : ℝ))*∑n∈range L,
        if ∀j∈B,(n : ZMod (p j))=z j then
          f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0 := by
  simp only [liftPiece,← mul_sum]
  rw [sum_comm]
  have he (n : ℕ) : (∑W∈B.powerset,f n*exactGate p (U∪W)
      (coordinateFreeze p B z x-fun j => (n : ZMod (p j))))=
      (∏j∈B,p j : ℝ)*(if ∀j∈B,(n : ZMod (p j))=z j then
        f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0) := by
    rw [← mul_sum,coordinateFreeze_sub,sum_exactGate_frozen p U B hUB]
    simp only [Pi.sub_apply,sub_eq_zero,eq_comm (a:=z _) ]
    split_ifs <;> ring
  simp_rw [he]
  rw [← mul_sum]
  ring

lemma residueGate_mul_unit {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (j : J) (u : (ZMod (p j))ˣ) (x : ZMod (p j)) :
    residueGate (p j) ((u : ZMod (p j))*x)=residueGate (p j) x := by
  unfold residueGate
  simp only [Units.mul_right_eq_zero]

lemma exactGate_affine (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (z c t : ResidueSpace p) :
    exactGate p U (z-(fun j => c j+(u j : ZMod (p j))*t j))=
      exactGate p U (fun j => ((u j)⁻¹ : (ZMod (p j))ˣ)*(z j-c j)-t j) := by
  apply prod_congr rfl
  intro j hj
  have he : z j-(c j+(u j : ZMod (p j))*t j)=
      (u j : ZMod (p j))*(((u j)⁻¹ : (ZMod (p j))ˣ)*(z j-c j)-t j) := by
    rw [mul_sub,← mul_assoc,Units.mul_inv,one_mul]
    ring
  change residueGate (p j) (z j-(c j+(u j : ZMod (p j))*t j))=_
  rw [he,residueGate_mul_unit]

lemma exactGate_square_progression (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (D c t : ℕ) (hu : ∀j,(u j : ZMod (p j))=(D : ZMod (p j))^2)
    (x : ResidueSpace p) :
    exactGate p U (x-fun j => ((c+D^2*t : ℕ) : ZMod (p j)))=
      exactGate p U ((fun j => ((u j)⁻¹ : (ZMod (p j))ˣ)*(x j-(c : ZMod (p j))))-
        fun j => (t : ZMod (p j))) := by
  have he := exactGate_affine p U u x (fun j => (c : ZMod (p j)))
    (fun j => (t : ZMod (p j)))
  convert he using 2 ; ext j ; simp [hu]

lemma fiber_squareStep_lift (N D L a : ℕ) (hD : 0<D) (hL : 0<L) (ha : a<D)
    (hNL : N≤D^2*L) (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0)
    (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (hu : ∀j,(u j : ZMod (p j))=(D : ZMod (p j))^2) (x : ResidueSpace p) :
    ((D : ℝ)/(N : ℝ))*∑n∈range N,
      (if n%D=a then f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0)=
    ((D : ℝ)*(L : ℝ)/(N : ℝ))*∑j∈range D,
      liftPiece p L (fun t => f (a+D*j+D^2*t)) U
        (fun k => ((u k)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j : ℕ) : ZMod (p k)))) := by
  rw [squareStep_padded_sum (fun n => f n*exactGate p U (x-fun j => (n : ZMod (p j))))
    N D L a hD ha hNL (fun n hn => by rw [hf n hn,zero_mul])]
  simp only [liftPiece,exactGate_square_progression p U u D _ _ hu,← mul_sum]
  have hL0 : (L : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
  field_simp

end Fiber

end SquareDifference

end LiftAnalysis

namespace SquareDifference

open Finset

section FrozenAnalysis

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

noncomputable def freezeCoordinates (B : Finset J) (z x : ∀j,X j) : ∀j,X j :=
  fun j => if j∈B then z j else x j

lemma freeze_update_outside {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (B : Finset J) (z x : ∀j,X j) (j : J) (hj : j∉B) (t : X j) :
    freezeCoordinates B z (Function.update x j t)=Function.update (freezeCoordinates B z x) j t := by
  ext i
  by_cases hi : i=j
  · subst i; simp [freezeCoordinates,hj]
  · simp [freezeCoordinates,hi]

lemma freeze_update_inside {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (B : Finset J) (z x : ∀j,X j) (j : J) (hj : j∈B) (t : X j) :
    freezeCoordinates B z (Function.update x j t)=freezeCoordinates B z x := by
  ext i
  by_cases hi : i=j
  · subst i; simp [freezeCoordinates,hj]
  · simp [freezeCoordinates,hi]

lemma ExactSupport.freeze (U B : Finset J) (f : (∀j,X j) → ℝ) (hf : ExactSupport U f)
    (z : ∀j,X j) : ExactSupport (U\B) (fun x => f (freezeCoordinates B z x)) := by
  constructor
  · intro j hj x
    rw [mem_sdiff] at hj
    simp only [freeze_update_outside B z x j hj.2]
    exact hf.1 j hj.1 _
  · intro j hj x t
    change f (freezeCoordinates B z (Function.update x j t))=f (freezeCoordinates B z x)
    by_cases hjB : j∈B
    · rw [freeze_update_inside B z x j hjB t]
    · rw [freeze_update_outside B z x j hjB t]
      exact hf.2 j (fun h => hj (mem_sdiff.mpr ⟨h,hjB⟩)) _ t

lemma ExactSupport.finset_sum {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] {I : Type*} (s : Finset I) (U : Finset J)
    (f : I → (∀j,X j) → ℝ) (hf : ∀i∈s,ExactSupport U (f i)) :
    ExactSupport U (fun x => ∑i∈s,f i x) := by
  constructor
  · intro j hj x
    rw [expect_sum_comm]
    exact sum_eq_zero (fun i hi => (hf i hi).1 j hj x)
  · intro j hj x t
    exact sum_congr rfl (fun i hi => (hf i hi).2 j hj x t)

lemma expect_fixed_update_le {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (F : (∀j,X j) → ℝ) (hF : ∀x,0≤F x) (j : J) (t : X j) :
    (𝔼 x,F (Function.update x j t))≤(Fintype.card (X j) : ℝ)*(𝔼 x,F x) := by
  have hc : (Fintype.card (X j) : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ 𝔼 x,(Fintype.card (X j) : ℝ)*(𝔼 u : X j,F (Function.update x j u)) := by
      apply expect_le_expect
      intro x _
      rw [expect_eq_sum_div_card,card_univ,mul_div_cancel₀ _ hc]
      exact single_le_sum (fun u _ => hF _) (mem_univ t)
    _ = _ := by rw [← mul_expect,expect_update_dep]

lemma expect_freeze_le (F : (∀j,X j) → ℝ) (hF : ∀x,0≤F x) (B : Finset J) (z : ∀j,X j) :
    (𝔼 x,F (freezeCoordinates B z x))≤(∏j∈B,(Fintype.card (X j) : ℝ))*(𝔼 x,F x) := by
  induction B using Finset.induction_on with
  | empty =>
    have he (x : ∀j,X j) : freezeCoordinates ∅ z x=x := by ext j; simp [freezeCoordinates]
    simp only [he,prod_empty,one_mul,le_refl]
  | @insert j B hj ih =>
    have he (x : ∀j,X j) : freezeCoordinates (insert j B) z x=
        freezeCoordinates B z (Function.update x j (z j)) := by
      ext i
      by_cases hi : i=j
      · subst i; simp [freezeCoordinates,hj]
      · simp [freezeCoordinates,hi]
    simp_rw [he]
    apply (expect_fixed_update_le (fun x => F (freezeCoordinates B z x)) (fun x => hF _) j (z j)).trans
    rw [prod_insert hj,mul_assoc]
    exact mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)

end FrozenAnalysis

lemma grouped_conditional_decay {J I V : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq I] [Fintype V] [DecidableEq V]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : ZMod (p j) → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (v : V)
    (hmix : ∀j (f : ZMod (p j) → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (p j : ℝ)^(-(1:ℝ)/32)*(𝔼 x,f x^2))
    (s : Finset I) (σ : I → Finset J) (f : I → (∀j,ZMod (p j)) → ℝ)
    (hf : ∀i∈s,ExactSupport (σ i) (f i)) (T : ℝ) (hT : 0<T)
    (hden : ∀i∈s,T≤(∏j∈σ i,p j : ℝ)) :
    conditionalEnergy (jointDensity (tensorLaw L) (Equiv.funSplitAt v _)) (fun x => ∑i∈s,f i x)≤
      T^(-(1:ℝ)/32)*(𝔼 x,(∑i∈s,f i x)^2) := by
  let g (U : Finset J) (x : ∀j,ZMod (p j)) := ∑i∈s.filter (fun i => σ i=U),f i x
  have hg (U : Finset J) (_hU : U∈s.image σ) : ExactSupport U (g U) := by
    apply ExactSupport.finset_sum
    intro i hi
    obtain ⟨his,hiU⟩ := mem_filter.mp hi
    simpa only [← hiU] using hf i his
  have he (x : ∀j,ZMod (p j)) : (∑U∈s.image σ,g U x)=∑i∈s,f i x := by
    exact sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem σ hi) (fun i => f i x)
  have hh := tensorLaw_prime_conductor_energy p L hL hmarg v hmix (s.image σ) g hg T hT
    (fun U hU => by obtain ⟨i,hi,rfl⟩ := mem_image.mp hU; exact hden i hi)
  simpa only [he] using hh

end SquareDifference

namespace SquareDifference

open Finset

lemma multilinearIntegral_slot {V X : Type*} [Fintype V] [DecidableEq V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (v : V) (F : V → X → ℝ) :
    multilinearIntegral L F=L (fun z => F v (z v)*∏w : {w : V // w≠v},F w (z w)) := by
  unfold multilinearIntegral
  congr 1; funext z
  rw [prod_eq_mul_prod_sdiff_singleton v _ (by simp)]
  congr 1
  exact prod_subtype (univ\{v}) (by intro w; simp) _

lemma multilinearIntegral_update_sub {V X : Type*} [Fintype V] [DecidableEq V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (v : V) (F : V → X → ℝ) (f g : X → ℝ) :
    multilinearIntegral L (Function.update F v f)-multilinearIntegral L (Function.update F v g)=
      L (fun z => (f (z v)-g (z v))*∏w : {w : V // w≠v},F w (z w)) := by
  rw [multilinearIntegral_slot L v,multilinearIntegral_slot L v,←map_sub]
  congr 1; funext z
  have hf (w : {w : V // w≠v}) : Function.update F v f (w:V)=F w := Function.update_of_ne w.property _ _
  have hg (w : {w : V // w≠v}) : Function.update F v g (w:V)=F w := Function.update_of_ne w.property _ _
  simp only [Function.update_self,hf,hg,Pi.sub_apply,sub_mul]

lemma multilinearIntegral_telescope {V X : Type*} [Fintype V] [DecidableEq V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : V → X → ℝ) (E : V → ℝ)
    (hslot : ∀v (A : V → X → ℝ),(∀w,A w=F w ∨ A w=G w) →
      |L (fun z => (F v (z v)-G v (z v))*∏w : {w : V // w≠v},A w (z w))|≤E v) :
    |multilinearIntegral L F-multilinearIntegral L G|≤∑v,E v := by
  have hb (S : Finset V) :
      |multilinearIntegral L (fun v => if v∈S then F v else G v)-multilinearIntegral L G|≤∑v∈S,E v := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert v S hv ih =>
      let A : V → X → ℝ := fun w => if w∈S then F w else G w
      have hA : ∀w,A w=F w ∨ A w=G w := by
        intro w
        dsimp [A]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hins : (fun w => if w∈insert v S then F w else G w)=Function.update A v (F v) := by
        funext w; by_cases hw : w=v
        · subst w; simp
        · simp [hw,A]
      have hbase : A=Function.update A v (G v) := by
        funext w; by_cases hw : w=v
        · subst w; simp [A,hv]
        · simp [hw]
      have hd : |multilinearIntegral L (fun w => if w∈insert v S then F w else G w)-
          multilinearIntegral L A|≤E v := by
        rw [hins]
        calc
          _ = |multilinearIntegral L (Function.update A v (F v))-
              multilinearIntegral L (Function.update A v (G v))| :=
            congrArg (fun t => |multilinearIntegral L (Function.update A v (F v))-t|)
              (congrArg (multilinearIntegral L) hbase)
          _ ≤ E v := by rw [multilinearIntegral_update_sub]; exact hslot v A hA
      rw [sum_insert hv]
      exact (abs_sub_le _ (multilinearIntegral L A) _).trans (add_le_add hd ih)
  simpa using hb univ

lemma diagonalRoot_zero {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : diagonalRoot L (0 : X → ℝ)=0 := by
  have hn : Fintype.card V≠0 := Fintype.card_ne_zero
  unfold diagonalRoot diagonalIntegral multilinearIntegral
  have he : (fun _z : V → X => ∏ _v : V, (0:ℝ))=(0 : (V → X) → ℝ) := by
    funext z; simp [hn]
  simp only [Pi.zero_apply,he,map_zero]
  exact Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.mpr hn))

lemma diagonalRoot_nonneg_smul {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (c : ℝ) (hc : 0≤c) (f : X → ℝ) : diagonalRoot L (c • f)=c*diagonalRoot L f := by
  unfold diagonalRoot
  rw [diagonalIntegral_smul,Real.mul_rpow (pow_nonneg hc _) (hd f)]
  congr 1
  rw [←Real.rpow_natCast_mul hc,mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),Real.rpow_one]

lemma diagonalRoot_sum_le {V X I : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (S : Finset I) (f : I → X → ℝ) : diagonalRoot L (∑i∈S,f i)≤∑i∈S,diagonalRoot L (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [sum_empty,diagonalRoot_zero,le_refl]
  | @insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi]
    exact (diagonalRoot_add_le L hd hh _ _).trans (add_le_add_right ih _)

lemma diagonalRoot_expect_le {V X I : Type*} [Fintype V] [Nonempty V]
    [Fintype I] [Nonempty I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (f : I → X → ℝ) : diagonalRoot L (fun x => 𝔼 i,f i x)≤𝔼 i,diagonalRoot L (f i) := by
  have he : (fun x => 𝔼 i,f i x)=(Fintype.card I : ℝ)⁻¹ • ∑i,f i := by
    funext x
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul,expect_eq_sum_div_card,card_univ,div_eq_inv_mul]
  rw [he,diagonalRoot_nonneg_smul L hd _ (by positivity),expect_eq_sum_div_card,card_univ,div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (diagonalRoot_sum_le L hd hh univ f) (by positivity)

end SquareDifference

namespace SquareDifference

open Finset

lemma multilinear_truncation_error {V X : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] [Fintype X] [Nonempty X] [DecidableEq X]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (F G : V → X → ℝ) (H q M : ℝ) (hH : 0<H) (hq : 0≤q) (hM : 0≤M)
    (henergy : ∀v,conditionalEnergy (jointDensity L (Equiv.funSplitAt v X)) (F v-G v)≤
      H^(-(1:ℝ)/32)*(q*M^2))
    (hm : ∀v w,L (fun z => |F w (z w)|^(2*Fintype.card {w : V // w≠v}))≤
        q*M^(2*Fintype.card {w : V // w≠v}) ∧
      L (fun z => |G w (z w)|^(2*Fintype.card {w : V // w≠v}))≤
        q*M^(2*Fintype.card {w : V // w≠v})) :
    |multilinearIntegral L F-multilinearIntegral L G|≤
      (Fintype.card V : ℝ)*H^(-(1:ℝ)/64)*q*M^(Fintype.card V) := by
  have hs (v : V) (A : V → X → ℝ) (hA : ∀w,A w=F w ∨ A w=G w) :
      |L (fun z => (F v (z v)-G v (z v))*∏w : {w : V // w≠v},A w (z w))|≤
        H^(-(1:ℝ)/64)*q*M^(Fintype.card V) := by
    obtain ⟨w,hw⟩ := exists_ne v
    let : Nonempty {w : V // w≠v} := ⟨⟨w,hw⟩⟩
    have hr : Fintype.card {w : V // w≠v}+1=Fintype.card V := by
      simp only [Fintype.card_subtype_compl,Fintype.card_unique]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    have hb := law_slot_product_sq v L hL (F v-G v) A
      (q*M^(2*Fintype.card {w : V // w≠v})) (fun w => by
        rcases hA w with h | h <;> rw [h]
        · exact (hm v w).1
        · exact (hm v w).2)
    have hc : (L (fun z => (F v (z v)-G v (z v))*∏w : {w : V // w≠v},A w (z w)))^2≤
        H^(-(1:ℝ)/32)*(q*M^2)*(q*M^(2*Fintype.card {w : V // w≠v})) :=
      hb.trans (mul_le_mul_of_nonneg_right (henergy v) (by positivity))
    have he : H^(-(1:ℝ)/32)*(q*M^2)*(q*M^(2*Fintype.card {w : V // w≠v}))=
        (H^(-(1:ℝ)/64)*q*M^(Fintype.card V))^2 := by
      rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hH.le]
      have hpow : M^2*M^(2*Fintype.card {w : V // w≠v})=(M^(Fintype.card V))^2 := by
        rw [←pow_add,←pow_mul]
        congr 1
        omega
      rw [show (-(1:ℝ)/64)*(2:ℕ)=-(1:ℝ)/32 by norm_num]
      calc
        _ = H^(-(1:ℝ)/32)*q^2*(M^2*M^(2*Fintype.card {w : V // w≠v})) := by ring
        _ = _ := by rw [hpow]
    rw [he] at hc
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hc)
  have ht := multilinearIntegral_telescope L F G (fun _ => H^(-(1:ℝ)/64)*q*M^(Fintype.card V)) hs
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_assoc] using ht

end SquareDifference

namespace LiftAnalysis

namespace SquareDifference

open Finset

lemma uniform_lift_moment_constant (r : ℕ) (hr : 1≤r) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀(F : Finset (Finset J)) (Q : ℕ),0<Q → (∀U∈F,∏j∈U,p j≤Q) →
      ∀L : ℕ,0<L → 2*(Q : ℝ)≤L → (Q : ℝ)^5≤L →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n<L,|f n|≤M) →
      (𝔼 x,(∑U∈F,liftPiece p L f U x)^(2*r))≤(C*M*(Q : ℝ)^ε)^(2*r) := by
  obtain ⟨T,hT⟩ := exists_nat_power_threshold ((4:ℝ)*2^(2*r)*5^r) (2*ε) (by positivity)
  refine ⟨2*((4:ℝ)*2^(2*r)*5^r)^T,by positivity,?_⟩
  intro J _ _ p _ hp hinj F Q hQ hden L hL hs hs' f M hM hf
  convert liftPiece_moment_uniform p hp hinj F Q hQ hden L hL hs hs' f M hM hf r hr ε hε.le T hT using 1
  congr 1; ring

section ActualLift

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def supportFamily (Q : ℕ) : Finset (Finset J) :=
  univ.filter (fun U => ∏j∈U,p j≤Q)

noncomputable def truncatedLift (L Q : ℕ) (f : ℕ → ℝ) (x : ResidueSpace p) : ℝ :=
  ∑U∈supportFamily p Q,liftPiece p L f U x

noncomputable def remainingFamily (B : Finset J) (H : ℕ) : Finset (Finset J) :=
  univ.filter (fun U => Disjoint U B ∧ ∏j∈U,p j≤H)

lemma primeProduct_pos {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (U : Finset J) : 0<∏j∈U,p j :=
  prod_pos (fun _ _ => Nat.pos_of_ne_zero (NeZero.ne _))

lemma primeProduct_mono {U W : Finset J} (h : U⊆W) : (∏j∈U,p j)≤∏j∈W,p j :=
  Nat.le_of_dvd (primeProduct_pos p W) (prod_dvd_prod_of_subset U W p h)

lemma primeProduct_split {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (T B : Finset J) : (∏j∈T,p j)=(∏j∈T\B,p j)*(∏j∈T∩B,p j) := by
  rw [←prod_union (disjoint_sdiff_inter T B),sdiff_union_inter]

lemma remaining_complete_sum {E : Type*} [AddCommMonoid E] (B : Finset J) (Q H : ℕ)
    (hHQ : H*(∏j∈B,p j)≤Q) (f : Finset J → E) :
    (∑T∈(supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),f T)=
      ∑U∈remainingFamily p B H,∑W∈B.powerset,f (U∪W) := by
  rw [←sum_product' (remainingFamily p B H) B.powerset (fun U W => f (U∪W))]
  apply sum_bij (fun T _ => (T\B,T∩B))
  · intro T hT
    obtain ⟨_,hTH⟩ := mem_filter.mp hT
    apply mem_product.mpr
    refine ⟨?_,mem_powerset.mpr inter_subset_right⟩
    simp only [remainingFamily,mem_filter,mem_univ,true_and]
    exact ⟨sdiff_disjoint,hTH⟩
  · intro T hT U hU he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp only at h1 h2
    have et : (T\B)∪(T∩B)=T := sdiff_union_inter T B
    have eu : (U\B)∪(U∩B)=U := sdiff_union_inter U B
    rw [←et,←eu,h1,h2]
  · rintro ⟨U,W⟩ hUW
    obtain ⟨hU,hW⟩ := mem_product.mp hUW
    obtain ⟨hUB,hUH⟩ : Disjoint U B ∧ ∏j∈U,p j≤H := by
      simpa only [remainingFamily,mem_filter,mem_univ,true_and] using hU
    have hWB := mem_powerset.mp hW
    have hdiff : (U∪W)\B=U := by
      ext j; simp only [mem_sdiff,mem_union]
      constructor
      · rintro ⟨h,hB⟩; exact h.resolve_right (fun hW => hB (hWB hW))
      · intro hU; exact ⟨Or.inl hU,disjoint_left.mp hUB hU⟩
    have hinter : (U∪W)∩B=W := by
      ext j; simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨h,hB⟩; exact h.resolve_left (fun hU => disjoint_left.mp hUB hU hB)
      · intro hW; exact ⟨Or.inr hW,hWB hW⟩
    refine ⟨U∪W,?_,Prod.ext hdiff hinter⟩
    simp only [mem_filter,supportFamily,mem_univ,true_and,hdiff]
    refine ⟨?_,hUH⟩
    rw [prod_union (hUB.mono_right hWB)]
    exact (Nat.mul_le_mul hUH (primeProduct_mono p hWB)).trans hHQ
  · intro T _
    congr 1
    exact (sdiff_union_inter T B).symm

lemma frozen_low_lift_identity (L Q H : ℕ) (f : ℕ → ℝ) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z x : ResidueSpace p) :
    (∑T∈(supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      liftPiece p L f T (coordinateFreeze p B z x))=
      ((∏j∈B,p j : ℝ)/(L : ℝ))*∑U∈remainingFamily p B H,∑n∈range L,
        if ∀j∈B,(n : ZMod (p j))=z j then
          f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0 := by
  rw [remaining_complete_sum p B Q H hHQ]
  simp only [mul_sum]
  apply sum_congr rfl
  intro U hU
  have hUB : Disjoint U B := (mem_filter.mp hU).2.1
  simpa only [mul_sum] using liftPiece_frozen_complete p L f U B hUB z x

lemma exactGate_square_progression_on (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (D c t : ℕ) (hu : ∀j∈U,(u j : ZMod (p j))=(D : ZMod (p j))^2)
    (x : ResidueSpace p) :
    exactGate p U (x-fun j => ((c+D^2*t : ℕ) : ZMod (p j)))=
      exactGate p U ((fun j => ((u j)⁻¹ : (ZMod (p j))ˣ)*(x j-(c : ZMod (p j))))-
        fun j => (t : ZMod (p j))) := by
  calc
    _ = exactGate p U (x-fun j => (c : ZMod (p j))+(u j : ZMod (p j))*(t : ZMod (p j))) := by
      apply prod_congr rfl
      intro j hj
      simp only [Pi.sub_apply,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,hu j hj]
    _ = _ := exactGate_affine p U u x (fun j => (c : ZMod (p j))) (fun j => (t : ZMod (p j)))

lemma fiber_squareStep_lift_on (N D L a : ℕ) (hD : 0<D) (hL : 0<L) (ha : a<D)
    (hNL : N≤D^2*L) (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0)
    (U : Finset J) (u : ∀j,(ZMod (p j))ˣ)
    (hu : ∀j∈U,(u j : ZMod (p j))=(D : ZMod (p j))^2) (x : ResidueSpace p) :
    ((D : ℝ)/(N : ℝ))*∑n∈range N,
      (if n%D=a then f n*exactGate p U (x-fun j => (n : ZMod (p j))) else 0)=
    ((D : ℝ)*(L : ℝ)/(N : ℝ))*∑j∈range D,
      liftPiece p L (fun t => f (a+D*j+D^2*t)) U
        (fun k => ((u k)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j : ℕ) : ZMod (p k)))) := by
  rw [squareStep_padded_sum (fun n => f n*exactGate p U (x-fun j => (n : ZMod (p j))))
    N D L a hD ha hNL (fun n hn => by rw [hf n hn,zero_mul])]
  simp only [liftPiece,exactGate_square_progression_on p U u D _ _ hu,←mul_sum]
  have hL0 : (L : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
  field_simp

end ActualLift

end SquareDifference

end LiftAnalysis

end

end OAI
