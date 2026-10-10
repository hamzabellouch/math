import OAI.Combinatorics.SquareDifference.ResidueLift

namespace OAI

section
open Finset
open scoped BigOperators

namespace SquareDifference

open Finset

section Projections

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

lemma ExactSupport.freeze_disjoint {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [∀ (j : J), Nonempty (X j)]
    [(j : J) → DecidableEq (X j)] (U B : Finset J) (f : (∀j,X j) → ℝ)
    (hf : ExactSupport U f) (hUB : Disjoint U B) (z x : ∀j,X j) :
    f (freezeCoordinates B z x)=f x := by
  induction B using Finset.induction_on with
  | empty => rfl
  | @insert j B hj ih =>
    have hjU : j∉U := fun hjU => disjoint_left.mp hUB hjU (mem_insert_self _ _)
    have hUB' := hUB.mono_right (subset_insert j B)
    have he : freezeCoordinates (insert j B) z x=Function.update (freezeCoordinates B z x) j (z j) := by
      ext i
      by_cases hij : i=j
      · subst i; simp [freezeCoordinates]
      · simp [freezeCoordinates,hij]
    rw [he,hf.2 j hjU]
    exact ih hUB'

lemma ExactSupport.project (U B : Finset J) (f : (∀j,X j) → ℝ)
    (hf : ExactSupport U f) (x : ∀j,X j) :
    (𝔼 z,f (freezeCoordinates B z x))=if Disjoint U B then f x else 0 := by
  classical
  by_cases hUB : Disjoint U B
  · simp only [hUB,ite_true,hf.freeze_disjoint U B f hUB,Fintype.expect_const]
  · rw [ite_eq_right hUB]
    obtain ⟨j,hjU,hjB⟩ := not_disjoint_iff.mp hUB
    rw [←expect_update_dep j (fun z => f (freezeCoordinates B z x))]
    have he (z : ∀j,X j) (t : X j) : freezeCoordinates B (Function.update z j t) x=
        Function.update (freezeCoordinates B z x) j t := by
      ext i
      by_cases hij : i=j
      · subst i; simp [freezeCoordinates,hjB]
      · simp [freezeCoordinates,hij]
    simp only [he,hf.1 j hjU,Fintype.expect_const]

end Projections

section GroupProjection

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,AddCommGroup (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

noncomputable def coordinateProjection (B : Finset J) (f : (∀j,X j) → ℝ) (x : ∀j,X j) : ℝ :=
  𝔼 z,f (freezeCoordinates B z x)

def maskedCoordinate (B : Finset J) (z : ∀j,X j) : ∀j,X j := fun j => if j∈B then z j else 0

lemma coordinateProjection_translates {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [(j : J) → AddCommGroup (X j)]
    [(j : J) → DecidableEq (X j)] (B : Finset J) (f : (∀j,X j) → ℝ) (x : ∀j,X j) :
    coordinateProjection B f x=𝔼 z,f (x+maskedCoordinate B z) := by
  unfold coordinateProjection
  have he (z : ∀j,X j) : freezeCoordinates B (x+z) x=x+maskedCoordinate B z := by
    ext j
    by_cases hj : j∈B <;> simp [freezeCoordinates,maskedCoordinate,hj]
  exact (Fintype.expect_equiv (Equiv.addLeft x)
    (fun z => f (x+maskedCoordinate B z)) (fun z => f (freezeCoordinates B z x))
    (fun z => congrArg f (he z).symm)).symm

lemma diagonalRoot_projection_le {V : Type*} [Fintype V] [Nonempty V]
    (L : ((V → ∀j,X j) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → (∀j,X j) → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (ht : ∀(a : ∀j,X j) F,L (fun z => F (fun v => z v+a))=L F)
    (B : Finset J) (f : (∀j,X j) → ℝ) :
    diagonalRoot L (coordinateProjection B f)≤diagonalRoot L f := by
  have he (a : ∀j,X j) : diagonalRoot L (fun x => f (x+a))=diagonalRoot L f := by
    unfold diagonalRoot diagonalIntegral multilinearIntegral
    rw [ht a (fun z => ∏v,f (z v))]
  have hfun : coordinateProjection B f=(fun x => 𝔼 z,f (x+maskedCoordinate B z)) :=
    funext (coordinateProjection_translates B f)
  rw [hfun]
  exact (diagonalRoot_expect_le L hd hh (fun z x => f (x+maskedCoordinate B z))).trans_eq (by simp only [he,Fintype.expect_const])

end GroupProjection

end SquareDifference

namespace SquareDifference

open Finset

section FrozenFamily

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

noncomputable def frozenFamily (B : Finset J) (z : ∀j,ZMod (p j))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ) (x : ∀j,ZMod (p j)) : ℝ :=
  ∑U∈s,f U (freezeCoordinates B z x)

lemma frozenFamily_moment (B : Finset J) (z : ∀j,ZMod (p j))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ)
    (r : ℕ) (M : ℝ) (hm : (𝔼 x,(∑U∈s,f U x)^(2*r))≤M^(2*r)) :
    (𝔼 x,frozenFamily p B z s f x^(2*r))≤(∏j∈B,p j : ℝ)*M^(2*r) := by
  have hh := expect_freeze_le (fun x => (∑U∈s,f U x)^(2*r))
    (fun x => Even.pow_nonneg (even_two_mul r) _) B z
  simp only [ZMod.card] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hm (prod_nonneg (fun _ _ => Nat.cast_nonneg _)))

lemma frozenFamily_sub_filter {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (B : Finset J) (z : ∀j,ZMod (p j))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ)
    (H : ℝ) :
    frozenFamily p B z s f-frozenFamily p B z (s.filter (fun U => (∏j∈U\B,p j : ℝ)≤H)) f=
      frozenFamily p B z (s.filter (fun U => H<(∏j∈U\B,p j : ℝ))) f := by
  funext x
  have he := sum_filter_add_sum_filter_not s (fun U => (∏j∈U\B,p j : ℝ)≤H)
    (fun U => f U (freezeCoordinates B z x))
  simp only [not_le] at he
  change (∑U∈s,f U (freezeCoordinates B z x))-(∑U∈s.filter _,f U (freezeCoordinates B z x))=
    ∑U∈s.filter _,f U (freezeCoordinates B z x)
  linarith

lemma frozen_family_telescope {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : ZMod (p j) → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (hmix : ∀j v (f : ZMod (p j) → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (p j : ℝ)^(-(1:ℝ)/32)*(𝔼 x,f x^2))
    (s : Finset (Finset J)) (f : V → Finset J → (∀j,ZMod (p j)) → ℝ)
    (hf : ∀v U, U∈s → ExactSupport U (f v U))
    (B : Finset J) (z : V → ∀j,ZMod (p j)) (H M : ℝ) (hH : 0<H) (hM : 0≤M)
    (hm : ∀v t,t⊆s → ∀r,r=1 ∨ r+1=Fintype.card V →
      (𝔼 x,(∑U∈t,f v U x)^(2*r))≤M^(2*r)) :
    |multilinearIntegral (tensorLaw L) (fun v => frozenFamily p B (z v) s (f v))-
      multilinearIntegral (tensorLaw L) (fun v => frozenFamily p B (z v)
        (s.filter (fun U => (∏j∈U\B,p j : ℝ)≤H)) (f v))|≤
      (Fintype.card V : ℝ)*H^(-(1:ℝ)/64)*(∏j∈B,p j : ℝ)*M^(Fintype.card V) := by
  apply multilinear_truncation_error (tensorLaw L) (tensorLaw_nonneg L hL) _ _ H _ M hH
    (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hM
  · intro v
    rw [frozenFamily_sub_filter]
    have he := grouped_conditional_decay p L hL hmarg v (fun j => hmix j v)
      (s.filter (fun U => H<(∏j∈U\B,p j : ℝ))) (fun U => U\B)
      (fun U x => f v U (freezeCoordinates B (z v) x))
      (fun U hU => (hf v U (mem_filter.mp hU).1).freeze U B (f v U) (z v)) H hH
      (fun U hU => (mem_filter.mp hU).2.le)
    have hm' := frozenFamily_moment p B (z v) (s.filter (fun U => H<(∏j∈U\B,p j : ℝ)))
      (f v) 1 M (hm v _ (filter_subset _ _) 1 (Or.inl rfl))
    norm_num only [mul_one] at hm'
    exact he.trans (mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hH.le _))
  · intro v w
    have hr : Fintype.card {w : V // w≠v}+1=Fintype.card V := by
      simp only [Fintype.card_subtype_compl,Fintype.card_unique]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    have he (t : Finset (Finset J)) :
        tensorLaw L (fun x => |frozenFamily p B (z w) t (f w) (x w)|^(2*Fintype.card {w : V // w≠v}))=
        𝔼 x,frozenFamily p B (z w) t (f w) x^(2*Fintype.card {w : V // w≠v}) := by
      have h := tensorLaw_marginal L w (fun j => hmarg j w)
        (fun x => |frozenFamily p B (z w) t (f w) x|^(2*Fintype.card {w : V // w≠v}))
      simpa only [(even_two_mul (Fintype.card {w : V // w≠v})).pow_abs] using h
    rw [he s,he (s.filter (fun U => (∏j∈U\B,p j : ℝ)≤H))]
    exact ⟨frozenFamily_moment p B (z w) s (f w) _ M (hm w s (Subset.refl _) _ (Or.inr hr)),
      frozenFamily_moment p B (z w) _ (f w) _ M (hm w _ (filter_subset _ _) _ (Or.inr hr))⟩

end FrozenFamily

end SquareDifference

namespace SquareDifference

open Finset

noncomputable abbrev liftSupportFamily {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.supportFamily p

noncomputable abbrev actualLiftPiece {J : Type*} [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.liftPiece p

noncomputable abbrev actualTruncatedLift {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.truncatedLift p

noncomputable abbrev actualRemainingFamily {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.remainingFamily p

section LiftProjection

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime]

lemma actualLiftPiece_exactSupport {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    ExactSupport U (actualLiftPiece p L f U) :=
  LiftAnalysis.SquareDifference.liftPiece_exactSupport p L f U

lemma actualLift_projection (L Q : ℕ) (f : ℕ → ℝ) (B : Finset J) :
    coordinateProjection B (actualTruncatedLift p L Q f)=
      (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x) := by
  funext x
  unfold coordinateProjection
  change (𝔼 z,∑U∈liftSupportFamily p Q,actualLiftPiece p L f U (freezeCoordinates B z x))=_
  rw [expect_sum_comm]
  simp only [(actualLiftPiece_exactSupport p L f _).project _ B _ x]
  rw [←sum_filter]
  apply sum_congr
  · ext U
    simp only [Finset.mem_filter, LiftAnalysis.SquareDifference.supportFamily,
      LiftAnalysis.SquareDifference.remainingFamily,mem_univ,true_and]
    exact and_comm
  · intro U hU; rfl

lemma actualLift_projection_diagonal_le (hp : ∀j,tupleReflectionThreshold≤(p j : ℝ))
    (L Q : ℕ) (f : ℕ → ℝ) (B : Finset J) :
    diagonalIntegral (productTupleLaw p)
      (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x)≤
      diagonalIntegral (productTupleLaw p) (actualTruncatedLift p L Q f) := by
  rw [←actualLift_projection]
  have hh := diagonalRoot_projection_le (productTupleLaw p) (productTupleLaw_diagonal_nonneg p hp)
    (productTupleLaw_signed_holder p hp)
    (fun a F => by simpa only [one_pow,one_mul,Pi.add_def] using productTupleLaw_affine p (fun _ => 1) a (by intro j; exact one_ne_zero) F)
    B (actualTruncatedLift p L Q f)
  have hpow := pow_le_pow_left₀ (diagonalRoot_nonneg _ (productTupleLaw_diagonal_nonneg p hp) _) hh (Fintype.card TupleVertex)
  simpa only [diagonalRoot_pow _ (productTupleLaw_diagonal_nonneg p hp)] using hpow

end LiftProjection

lemma uniform_common_lift_moments {V : Type} [Fintype V] [Nontrivial V]
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,NeZero (p j)], (Pairwise fun i j => (p i).Coprime (p j)) → Function.Injective p →
      ∀(s : Finset (Finset J)) (Q : ℕ),0<Q → (∀U∈s,∏j∈U,p j≤Q) →
      ∀L : ℕ,0<L → 2*(Q : ℝ)≤L → (Q : ℝ)^5≤L →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n<L,|f n|≤M) →
      ∀r,r=1 ∨ r+1=Fintype.card V →
      (𝔼 x,(∑U∈s,actualLiftPiece p L f U x)^(2*r))≤(C*M*(Q : ℝ)^ε)^(2*r) := by
  have hd : 1<Fintype.card V := Fintype.one_lt_card
  obtain ⟨C₁,hC₁,h₁⟩ := LiftAnalysis.SquareDifference.uniform_lift_moment_constant 1 (by omega) ε hε
  obtain ⟨C₂,hC₂,h₂⟩ := LiftAnalysis.SquareDifference.uniform_lift_moment_constant
    (Fintype.card V-1) (by omega) ε hε
  refine ⟨max C₁ C₂,lt_max_of_lt_left hC₁,?_⟩
  intro J _ _ p _ hp hinj s Q hQ hden L hL hs hs' f M hM hf r hr
  rcases hr with rfl | hr
  · apply (h₁ p hp hinj s Q hQ hden L hL hs hs' f M hM hf).trans
    gcongr
    exact le_max_left _ _
  · have he : r=Fintype.card V-1 := by omega
    subst r
    apply (h₂ p hp hinj s Q hQ hden L hL hs hs' f M hM hf).trans
    gcongr
    exact le_max_right _ _

end SquareDifference

namespace SquareDifference

open Finset

section LowFiber

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,NeZero (p j)]

lemma actual_low_lift_affine_sum
    (N Q H D L a : ℕ) (B : Finset J) (z : ∀j,ZMod (p j))
    (hHQ : H*(∏j∈B,p j)≤Q) (hD : 0<D) (hL : 0<L) (ha : a<D)
    (hNL : N≤D^2*L) (f f₀ : ℕ → ℝ) (hf : ∀n,N≤n → f₀ n=0)
    (hres : ∀n,(∏j∈B,p j : ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then f n else 0)=
      (D:ℝ)*(if n%D=a then f₀ n else 0))
    (u : ∀j,(ZMod (p j))ˣ) (hu : ∀j,j∉B → (u j:ZMod (p j))=(D:ZMod (p j))^2)
    (x : ∀j,ZMod (p j)) :
    (∑T∈(liftSupportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      actualLiftPiece p N f T (freezeCoordinates B z x))=
      ((D:ℝ)*(L:ℝ)/(N:ℝ))*∑j∈range D,
        ∑U∈actualRemainingFamily p B H,
          actualLiftPiece p L (fun t => f₀ (a+D*j+D^2*t)) U
            (fun k => ((u k)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j:ℕ):ZMod (p k)))) := by
  change (∑T∈(LiftAnalysis.SquareDifference.supportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
    LiftAnalysis.SquareDifference.liftPiece p N f T
      (LiftAnalysis.SquareDifference.coordinateFreeze p B z x))=_
  rw [LiftAnalysis.SquareDifference.frozen_low_lift_identity p N Q H f B hHQ z x]
  have he (U : Finset J) :
      ((∏j∈B,p j : ℝ)/(N:ℝ))*∑n∈range N,
        (if ∀j∈B,(n:ZMod (p j))=z j then f n*LiftAnalysis.SquareDifference.exactGate p U (x-fun j => (n:ZMod (p j))) else 0)=
      ((D:ℝ)/(N:ℝ))*∑n∈range N,
        (if n%D=a then f₀ n*LiftAnalysis.SquareDifference.exactGate p U (x-fun j => (n:ZMod (p j))) else 0) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro n _
    have hh := congrArg (fun y : ℝ => y*LiftAnalysis.SquareDifference.exactGate p U
      (x-fun j => (n:ZMod (p j)))/(N:ℝ)) (hres n)
    convert hh using 1 <;> split_ifs <;> ring
  rw [mul_sum]
  simp_rw [he]
  have he₂ (U : Finset J) (hU : U∈actualRemainingFamily p B H) :=
    LiftAnalysis.SquareDifference.fiber_squareStep_lift_on p N D L a hD hL ha hNL f₀ hf U u
      (fun j hj => hu j (Finset.disjoint_left.mp (Finset.mem_filter.mp hU).2.1 hj)) x
  simp_rw [sum_congr rfl he₂]
  rw [←mul_sum,sum_comm]

end LowFiber

end SquareDifference

namespace SquareDifference

open Finset

lemma diagonalIntegral_average_le {V X I : Type*} [Fintype V] [Nonempty V]
    [Fintype I] [Nonempty I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (f : I → X → ℝ) (K : ℝ) (hK : 0≤K) (hf : ∀i,diagonalIntegral L (f i)≤K) :
    diagonalIntegral L (fun x => 𝔼 i,f i x)≤K := by
  have he : diagonalRoot L (fun x => 𝔼 i,f i x)≤K^((1:ℝ)/(Fintype.card V:ℝ)) := by
    apply (diagonalRoot_expect_le L hd hh f).trans
    apply le_trans (expect_le_expect (fun i _ => Real.rpow_le_rpow (hd (f i)) (hf i) (by positivity)))
    rw [Fintype.expect_const]
  have hp := pow_le_pow_left₀ (diagonalRoot_nonneg L hd _) he (Fintype.card V)
  rw [diagonalRoot_pow L hd,←Real.rpow_mul_natCast hK,
    one_div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),Real.rpow_one] at hp
  exact hp

lemma diagonalRoot_change_variables {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (e : X → X)
    (he : ∀F,L (fun z => F (fun v => e (z v)))=L F) (f : X → ℝ) :
    diagonalRoot L (fun x => f (e x))=diagonalRoot L f := by
  unfold diagonalRoot diagonalIntegral multilinearIntegral
  rw [he (fun z => ∏v,f (z v))]

lemma diagonalIntegral_change_variables {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (e : X → X)
    (he : ∀F,L (fun z => F (fun v => e (z v)))=L F) (f : X → ℝ) :
    diagonalIntegral L (fun x => f (e x))=diagonalIntegral L f := by
  exact he (fun z => ∏v,f (z v))

lemma diagonalIntegral_affine_average_le {V X I : Type*} [Fintype V] [Nonempty V]
    [Fintype I] [Nonempty I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hd : ∀g,0≤diagonalIntegral L g)
    (hh : ∀A : V → X → ℝ,|multilinearIntegral L A|≤∏v,diagonalRoot L (A v))
    (f : I → X → ℝ) (e : I → X → X) (he : ∀i F,L (fun z => F (fun v => e i (z v)))=L F)
    (K lam : ℝ) (hK : 0≤K) (hlam : 0≤lam) (hf : ∀i,diagonalIntegral L (f i)≤K) :
    diagonalIntegral L (fun x => lam*(𝔼 i,f i (e i x)))≤lam^(Fintype.card V)*K := by
  change diagonalIntegral L (lam • (fun x => 𝔼 i,f i (e i x)))≤_
  rw [diagonalIntegral_smul]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
  apply diagonalIntegral_average_le L hd hh _ K hK
  intro i
  rw [diagonalIntegral_change_variables L (e i) (he i)]
  exact hf i

end SquareDifference

namespace SquareDifference

open Finset

instance tupleVertexNontrivial : Nontrivial TupleVertex := by
  refine ⟨⟨cycleVertex 0,cycleVertex 1,?_⟩⟩
  intro h
  apply tupleCycle_ne_one
  have he := congrFun h (⟨0,by decide⟩ : Fin tupleBlocks)
  simpa only [cycleVertex,pow_zero,pow_one] using he.symm

section ActualTails

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actual_frozen_lift_error (hp : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (L Q H : ℕ) (hH : 0<H) (f : TupleVertex → ℕ → ℝ) (B : Finset J)
    (z : TupleVertex → ∀j,ZMod (p j)) (M : ℝ) (hM : 0≤M)
    (hm : ∀v t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L (f v) U x)^(2*r))≤M^(2*r)) :
    |multilinearIntegral (productTupleLaw p) (fun v x => actualTruncatedLift p L Q (f v) (freezeCoordinates B (z v) x))-
      multilinearIntegral (productTupleLaw p) (fun v x =>
        ∑U∈(liftSupportFamily p Q).filter (fun U => ∏j∈U\B,p j≤H),
          actualLiftPiece p L (f v) U (freezeCoordinates B (z v) x))|≤
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈B,p j:ℝ)*M^(Fintype.card TupleVertex) := by
  have hh := frozen_family_telescope p (fun j => (tupleLaw (p:=p j)))
    (fun _ => tupleLaw_nonneg) (fun j => tupleLaw_marginal ((le_max_left _ _).trans (hp j)))
    (fun j => tupleLaw_conditional (hp j)) (liftSupportFamily p Q)
    (fun v U => actualLiftPiece p L (f v) U)
    (fun v U _ => actualLiftPiece_exactSupport p L (f v) U) B z (H:ℝ) M
    (by exact_mod_cast hH) hM hm
  convert hh using 1
  congr 3
  funext v x
  congr 1
  ext U
  simp only [mem_filter,←Nat.cast_prod,Nat.cast_le]

lemma actual_projected_lift_error (hp : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (L Q H : ℕ) (hH : 0<H) (hHQ : H≤Q) (f : ℕ → ℝ) (B : Finset J)
    (M : ℝ) (hM : 0≤M)
    (hm : ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L f U x)^(2*r))≤M^(2*r)) :
    |diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B H,actualLiftPiece p L f U x)-
      diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x)|≤
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M^(Fintype.card TupleVertex) := by
  have hsub : actualRemainingFamily p B Q⊆liftSupportFamily p Q := by
    intro U hU
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hU).2.2⟩
  have hh := frozen_family_telescope p (fun j => (tupleLaw (p:=p j)))
    (fun _ => tupleLaw_nonneg) (fun j => tupleLaw_marginal ((le_max_left _ _).trans (hp j)))
    (fun j => tupleLaw_conditional (hp j)) (actualRemainingFamily p B Q)
    (fun (_v : TupleVertex) U => actualLiftPiece p L f U)
    (fun _ U _ => actualLiftPiece_exactSupport p L f U) ∅ (fun _ => 0) (H:ℝ) M
    (by exact_mod_cast hH) hM (fun _ t ht => hm t (ht.trans hsub))
  have hfilt : (actualRemainingFamily p B Q).filter (fun U => (∏j∈U\∅,p j:ℝ)≤H)=actualRemainingFamily p B H := by
    ext U
    simp only [LiftAnalysis.SquareDifference.remainingFamily,mem_filter,mem_univ,true_and,
      sdiff_empty,←Nat.cast_prod,Nat.cast_le]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₁,h₃⟩
    · rintro ⟨h₁,h₂⟩; exact ⟨⟨h₁,h₂.trans hHQ⟩,h₂⟩
  rw [hfilt] at hh
  change |diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B Q,actualLiftPiece p L f U x)-
    diagonalIntegral (productTupleLaw p) (fun x => ∑U∈actualRemainingFamily p B H,actualLiftPiece p L f U x)|≤
    (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈(∅:Finset J),p j:ℝ)*M^(Fintype.card TupleVertex) at hh
  simp only [prod_empty,mul_one] at hh
  simpa only [diagonalIntegral,abs_sub_comm] using hh

lemma productTupleLaw_inverse_square (w : ∀j,(ZMod (p j))ˣ) (c : ∀j,ZMod (p j))
    (F : (TupleVertex → ∀j,ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => F (fun v j => (((w j)^2)⁻¹ : (ZMod (p j))ˣ)*(z v j-c j)))=
      productTupleLaw p F := by
  have he := productTupleLaw_affine p (fun j => ((w j)⁻¹ : (ZMod (p j))ˣ))
    (fun j => -(((w j)⁻¹ : (ZMod (p j))ˣ):ZMod (p j))^2*c j)
    (fun j => Units.ne_zero _) F
  convert he using 1
  congr 1
  funext z
  congr 1
  funext v j
  simp only [mul_sub,Units.val_inv_eq_inv_val,Units.val_pow_eq_pow_val,inv_pow]
  ring

end ActualTails

end SquareDifference

namespace SquareDifference

open Finset

lemma scale_sum_eq_expect {D : ℕ} (hD : 0<D) (L N : ℕ) (f : Fin D → ℝ) :
    ((D:ℝ)*L/N)*(∑j,f j)=((D:ℝ)^2*L/N)*(𝔼 j,f j) := by
  have hn : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  rw [expect_eq_sum_div_card,card_univ,Fintype.card_fin]
  field_simp

lemma diagonal_transfer_close {x y E K : ℝ} (h : |x-y|≤E) (hy : y≤K) : x≤K+E := by
  linarith [le_abs_self (x-y)]

section ActualTransfer

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma actual_frozen_diagonal_transfer
    (hp : ∀j,tupleConditionalThreshold≤(p j:ℝ))
    (href : ∀j,tupleReflectionThreshold≤(p j:ℝ))
    (N Q H D L Qc a : ℕ) (B : Finset J) (z : ∀j,ZMod (p j))
    (hH : 0<H) (hHQ : H*(∏j∈B,p j)≤Q) (hHQc : H≤Qc)
    (hD : 0<D) (hL : 0<L) (ha : a<D) (hNL : N≤D^2*L)
    (f f₀ : ℕ → ℝ) (hf : ∀n,N≤n → f₀ n=0)
    (hres : ∀n,(∏j∈B,p j:ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then f n else 0)=
      (D:ℝ)*(if n%D=a then f₀ n else 0))
    (w : ∀j,(ZMod (p j))ˣ) (hw : ∀j,j∉B → (w j:ZMod (p j))=(D:ZMod (p j)))
    (K M₁ M₂ : ℝ) (hK : 0≤K) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hm₁ : ∀t,t⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p N f U x)^(2*r))≤M₁^(2*r))
    (hm₂ : ∀j<D,∀t,t⊆liftSupportFamily p Qc → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈t,actualLiftPiece p L (fun t => f₀ (a+D*j+D^2*t)) U x)^(2*r))≤M₂^(2*r))
    (hchild : ∀j<D,diagonalIntegral (productTupleLaw p)
      (actualTruncatedLift p L Qc (fun t => f₀ (a+D*j+D^2*t)))≤K) :
    diagonalIntegral (productTupleLaw p)
      (fun x => actualTruncatedLift p N Q f (freezeCoordinates B z x))≤
      ((D:ℝ)^2*L/N)^(Fintype.card TupleVertex)*
        (K+(Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M₂^(Fintype.card TupleVertex))+
      (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*(∏j∈B,p j:ℝ)*M₁^(Fintype.card TupleVertex) := by
  let : NeZero D := ⟨hD.ne'⟩
  let E : ℝ := (Fintype.card TupleVertex:ℝ)*(H:ℝ)^(-(1:ℝ)/64)*M₂^(Fintype.card TupleVertex)
  let g (j : Fin D) (x : ∀j,ZMod (p j)) : ℝ :=
    ∑U∈actualRemainingFamily p B H,actualLiftPiece p L (fun t => f₀ (a+D*j.val+D^2*t)) U x
  let e (j : Fin D) (x : ∀j,ZMod (p j)) : ∀j,ZMod (p j) :=
    fun k => (((w k)^2)⁻¹ : (ZMod (p k))ˣ)*(x k-((a+D*j.val:ℕ):ZMod (p k)))
  have he (j : Fin D) (F : (TupleVertex → ∀j,ZMod (p j)) → ℝ) :
      productTupleLaw p (fun x => F (fun v => e j (x v)))=productTupleLaw p F :=
    productTupleLaw_inverse_square p w (fun k => ((a+D*j.val:ℕ):ZMod (p k))) F
  have hg (j : Fin D) : diagonalIntegral (productTupleLaw p) (g j)≤K+E := by
    have ht := actual_projected_lift_error p hp L Qc H hH hHQc
      (fun t => f₀ (a+D*j.val+D^2*t)) B M₂ hM₂ (hm₂ j.val j.isLt)
    have hc := (actualLift_projection_diagonal_le p href L Qc
      (fun t => f₀ (a+D*j.val+D^2*t)) B).trans (hchild j.val j.isLt)
    exact diagonal_transfer_close ht hc
  have hE : 0≤E := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg H) _)) (pow_nonneg hM₂ _)
  have hcoef : 0≤(D:ℝ)^2*L/N := div_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have havg := diagonalIntegral_affine_average_le (productTupleLaw p)
    (productTupleLaw_diagonal_nonneg p href) (productTupleLaw_signed_holder p href)
    g e he (K+E) ((D:ℝ)^2*L/N) (add_nonneg hK hE) hcoef hg
  have hid : (fun x => ∑T∈(liftSupportFamily p Q).filter (fun T => ∏j∈T\B,p j≤H),
      actualLiftPiece p N f T (freezeCoordinates B z x))=
      (fun x => ((D:ℝ)^2*L/N)*(𝔼 j,g j (e j x))) := by
    funext x
    rw [actual_low_lift_affine_sum p N Q H D L a B z hHQ hD hL ha hNL f f₀ hf hres
      (fun j => (w j)^2) (fun j hj => by simp only [Units.val_pow_eq_pow_val,hw j hj])]
    rw [←Fin.sum_univ_eq_sum_range]
    exact scale_sum_eq_expect hD L N (fun j => g j (e j x))
  have ht := actual_frozen_lift_error p hp N Q H hH (fun _ => f) B (fun _ => z) M₁ hM₁
    (fun _ => hm₁)
  rw [←hid] at havg
  dsimp only [E] at havg
  exact diagonal_transfer_close ht havg

end ActualTransfer

end SquareDifference

end

end OAI
