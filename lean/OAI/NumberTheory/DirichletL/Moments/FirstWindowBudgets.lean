import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalAnnularCommonBound

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstWindowBudgets
open CenteredMomentSecondWindowBudget

lemma sqrt_sum_le {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i):
    Real.sqrt (∑i∈s,E i)≤∑i∈s,Real.sqrt (E i):=by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he:0≤E a:=hE a (Finset.mem_insert_self _ _)
    have hs:0≤∑i∈s,E i:=Finset.sum_nonneg (fun i hi=>hE i (Finset.mem_insert_of_mem hi))
    have hadd:Real.sqrt (E a+∑i∈s,E i)≤Real.sqrt (E a)+Real.sqrt (∑i∈s,E i):=by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt he,Real.sq_sqrt hs,
          mul_nonneg (Real.sqrt_nonneg (E a)) (Real.sqrt_nonneg (∑i∈s,E i))]
    exact hadd.trans (add_le_add le_rfl (ih (fun i hi=>hE i (Finset.mem_insert_of_mem hi))))

lemma windowBudget_sum {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i)
    (J:ℕ)(t:ℝ):
    windowBudget J t (∑i∈s,E i)≤∑i∈s,windowBudget J t (E i):=by
  unfold windowBudget
  rw [←Finset.sum_mul,←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sqrt_sum_le s E hE) (pow_nonneg (heightEnvelope_pos t).le _))
    (profileMoment_nonneg J)

theorem windowBudget_pair_sum {α β:Type*}(s:Finset α)(u:Finset β)
    (E:α→ℝ)(F:β→ℝ)(hE:∀i∈s,0≤E i)(hF:∀j∈u,0≤F j)
    (J₁ J₂:ℕ)(t:ℝ):
    windowBudget J₁ t (∑i∈s,E i)*windowBudget J₂ t (∑j∈u,F j)≤
      ∑i∈s,∑j∈u,windowBudget J₁ t (E i)*windowBudget J₂ t (F j):=by
  have hh:=mul_le_mul (windowBudget_sum s E hE J₁ t) (windowBudget_sum u F hF J₂ t)
    (windowBudget_nonneg J₂ t _) (Finset.sum_nonneg (fun i _=>windowBudget_nonneg J₁ t (E i)))
  apply hh.trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

theorem actual_annular_block_from_four_budgets (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→Fin 4→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤E₁ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤E₂ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₁ L i)*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₂ L i)*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (E₁ L i)*windowBudget J₂ t (E₂ L j)) := by
  obtain ⟨Cb,hCb,hbound⟩:=CenteredMomentFirstPhysicalAnnularCommonBound.actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n
    (fun L=>∑i,E₁ L i) (fun L=>∑i,E₂ L i)
    (fun L hL=>Finset.sum_nonneg (fun i _=>hE₁ L hL i))
    (fun L hL=>Finset.sum_nonneg (fun i _=>hE₂ L hL i)) hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hCb)
  apply Finset.sum_le_sum
  intro L hL
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact windowBudget_pair_sum Finset.univ Finset.univ (E₁ L) (E₂ L)
    (fun i _=>hE₁ L hL i) (fun i _=>hE₂ L hL i) J₁ J₂ t

end SevenEighths.CenteredMomentFirstWindowBudgets

end

end OAI
