import OAI.NumberTheory.DirichletL.Moments.FirstRetainedPhysical

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedBlock
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CompletedGauss CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstCommonFourierTransport
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentSectorLocalization CenteredMomentFirstScale
local notation "O"=>ActualEisensteinCubic.O

lemma retained_tsum (R:ℝ)(f:O→ℂ):
    (∑'h:O,(retainedWeight R (normValue h):ℂ)*f h)=
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (retainedWeight R (normValue h):ℂ)*f h:=by
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (normValue h)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul] using hn
  simp only [hz,Complex.ofReal_zero,zero_mul]

lemma retainedFourierTerm_finite (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r ha hb hr χa χb G e E W K R=
      (UniqueFactorizationMonoid.moebius E:ℂ)*
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (tripleRow a b r χa χb G e *
          (((K/normValue e)/normValue (a*(b*r)):ℝ):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h)*
        (retainedWeight R (normValue h):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W
          ((K/normValue e)*normValue h/normValue (a*(b*r))):=by
  unfold retainedFourierTerm
  dsimp only
  simp_rw [mul_assoc (retainedWeight R (normValue _):ℂ)]
  rw [retained_tsum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [show (K/normValue e)/normValue (a*(b*r))*normValue h=
    (K/normValue e)*normValue h/normValue (a*(b*r)) by ring]
  ring

lemma finite_pair_row_sum {α β:Type*}[Fintype α][Fintype β]
    (rows:Finset O)(p:α→β→Prop)[DecidableRel p]
    (c:α→β→ℂ)(μ:ℂ)(f:α→β→O→ℂ):
    (∑a:α,∑b:β,if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
      μ*∑h∈rows,∑a:α,∑b:β,if p a b then c a b*f a b h else 0:=by
  have hp (a:α)(b:β):
      (if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
        ∑h∈rows,μ*(if p a b then c a b*f a b h else 0):=by
    by_cases hab:p a b
    · simp only [hab,ite_true,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    · simp [hab]
  simp_rw [hp,Finset.mul_sum]
  calc
    _=∑a:α,∑h∈rows,∑b:β,μ*(if p a b then c a b*f a b h else 0):=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=_:=Finset.sum_comm

theorem fixed_sector_term_block
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0)=
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedTerm
  generalize_proofs
  simp_rw [retainedFourierTerm_finite]
  rw [finite_pair_row_sum]
  rw [retainedInfiniteBlock_eq_finite]
  unfold retainedBlock inactiveWeight
  dsimp only
  simp only [normValue_eq_embedding]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> ring

theorem fixed_sector_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    fixedRetainedSector η m A t S c C D hC hD W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        retainedInfiniteBlock η m A t S c C D hC hD E W K
          (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedSector
  apply Finset.sum_congr rfl
  intro E hE
  exact fixed_sector_term_block η m A t S c C D hC hD E W K X Z ξ

end SevenEighths.CenteredMomentFirstRetainedBlock

end

end OAI
