import OAI.NumberTheory.DirichletL.Moments.ExceptionalSourceShell
import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalWholeSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentWholeDivisorShell
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalSourceShell
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma weight_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Source α)(v:Source κ)(D:Ideal O)
    (a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (Z r:ℝ)(hZ:0≤Z):0≤exceptionalWeight s v D a b Z r:=Real.rpow_nonneg hZ _

 theorem whole_weight_bound (lo hi:ι→ℝ)(B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Source I)(v:Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ∀r:ℝ,(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r):=by
  obtain ⟨Cs,hCs,hshell⟩:=exceptional_shell_subpower lo hi B (δ/2) hB (by linarith)
  obtain ⟨Cn,hCn,hcard⟩:=selected_card_subpower B (δ/2) hB (by linarith)
  refine ⟨Cn*Cs,mul_pos hCn hCs,?_⟩
  filter_upwards [hcard] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v hlo hhi Ds hDs r
  rw [sum_norm_moebius_shells]
  have hz:=zero_lt_one.trans hZ.1
  have hs (n:ℤ)(hn:n∈selectedShells Ds):
      (∑D∈shell Ds n,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤Cs*Z^(δ/2-r):=by
    have ht:=selected_scale_bounds Ds (Z^B) hDs n hn
    apply (Finset.sum_le_sum (fun D hD=>mul_le_of_le_one_left
      (Finset.sum_nonneg (fun a _=>Finset.sum_nonneg (fun b _=>weight_nonneg s v D a b Z r hz.le)))
      (moebius_norm_le_one D))).trans
    exact hshell I L s v hlo hhi (shell Ds n)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.1) (dyadicScale n) Z r ht.1 hZ.1 ht.2
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.1)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.2)
  calc
    _≤∑n∈selectedShells Ds,Cs*Z^(δ/2-r):=Finset.sum_le_sum hs
    _=((selectedShells Ds).card:ℝ)*(Cs*Z^(δ/2-r)):=by simp
    _≤(Cn*Z^(δ/2))*(Cs*Z^(δ/2-r)):=
      mul_le_mul_of_nonneg_right (hZ.2 Ds hDs) (mul_nonneg hCs.le (Real.rpow_nonneg hz.le _))
    _=(Cn*Cs)*Z^(δ-r):=by
      rw [show δ-r=δ/2+(δ/2-r) by ring,Real.rpow_add hz]
      ring

theorem actual_whole_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_amplitude ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z r:=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z r):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-r)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs r) hA
    _=_:=by
      rw [show 2*ε+δ-r=2*ε+(δ-r) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

end SevenEighths.CenteredMomentExceptionalWholeSource

end

end OAI
