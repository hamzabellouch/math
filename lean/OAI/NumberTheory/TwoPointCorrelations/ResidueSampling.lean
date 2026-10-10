import OAI.NumberTheory.TwoPointCorrelations.SieveCRT
import OAI.NumberTheory.TwoPointCorrelations.FiniteAverages

namespace OAI

/-! A fixed finite interval sample space for every sieve intersection.
The modulus may vary with the selected primes, but the actual sample law
in these identities never changes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def uniformFiniteLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := 1 / Fintype.card α
  nonneg _ := by positivity
  total := by simp [Fintype.card_ne_zero]

lemma uniformFiniteLaw_average {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (uniformFiniteLaw α).average f = uniformAverage f := by
  simp only [FiniteLaw.average, uniformFiniteLaw, ← mul_sum, uniformAverage]
  ring

lemma intervalResidueLaw_average_uniform {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (f : ZMod D → ℝ) :
    (intervalResidueLaw A N hN).average f =
      uniformAverage (fun j : Fin N => f (A + (j.val : ZMod D))) := by
  rw [intervalResidueLaw_average]
  unfold uniformAverage
  rw [Fintype.card_fin]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => f (A + (j : ZMod D))) N).symm

lemma uniformCube_average_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D × ZMod D × ZMod D)
    (f : (ZMod D × ZMod D × ZMod D) → ℝ) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).average
      (fun j => f (A.1 + (j.1.val : ZMod D),
        A.2.1 + (j.2.1.val : ZMod D), A.2.2 + (j.2.2.val : ZMod D))) =
      (residueCubeLaw A N (NeZero.pos N)).average f := by
  let μ₁ := intervalResidueLaw A.1 N (NeZero.pos N)
  let μ₂ := intervalResidueLaw A.2.1 N (NeZero.pos N)
  let μ₃ := intervalResidueLaw A.2.2 N (NeZero.pos N)
  have h₃ (i j : Fin N) :
      uniformAverage (fun k : Fin N => f (A.1 + (i.val : ZMod D),
        A.2.1 + (j.val : ZMod D), A.2.2 + (k.val : ZMod D))) =
      μ₃.average (fun z => f (A.1 + (i.val : ZMod D), A.2.1 + (j.val : ZMod D), z)) :=
    (intervalResidueLaw_average_uniform A.2.2 N (NeZero.pos N)
      (fun z => f (A.1 + (i.val : ZMod D), A.2.1 + (j.val : ZMod D), z))).symm
  have h₂ (i : Fin N) :
      uniformAverage (fun j : Fin N =>
        μ₃.average (fun z => f (A.1 + (i.val : ZMod D), A.2.1 + (j.val : ZMod D), z))) =
      μ₂.average (fun y => μ₃.average (fun z => f (A.1 + (i.val : ZMod D), y, z))) :=
    (intervalResidueLaw_average_uniform A.2.1 N (NeZero.pos N)
      (fun y => μ₃.average (fun z => f (A.1 + (i.val : ZMod D), y, z)))).symm
  have hprod (i : Fin N) := uniformAverage_prod
    (fun (j k : Fin N) => f (A.1 + (i.val : ZMod D),
      A.2.1 + (j.val : ZMod D), A.2.2 + (k.val : ZMod D)))
  rw [uniformFiniteLaw_average, uniformAverage_prod
    (fun (i : Fin N) (jk : Fin N × Fin N) => f (A.1 + (i.val : ZMod D),
      A.2.1 + (jk.1.val : ZMod D), A.2.2 + (jk.2.val : ZMod D)))]
  simp_rw [hprod, h₃, h₂]
  change _ = (μ₁.product (μ₂.product μ₃)).average f
  rw [FiniteLaw.average_product]
  simp_rw [FiniteLaw.average_product]
  exact (intervalResidueLaw_average_uniform A.1 N (NeZero.pos N)
    (fun x => μ₂.average (fun y => μ₃.average (fun z => f (x, y, z))))).symm

lemma uniformCube_probability_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D × ZMod D × ZMod D)
    (E : (ZMod D × ZMod D × ZMod D) → Prop) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
      (fun j => E (A.1 + (j.1.val : ZMod D),
        A.2.1 + (j.2.1.val : ZMod D), A.2.2 + (j.2.2.val : ZMod D))) =
      (residueCubeLaw A N (NeZero.pos N)).probability E :=
  uniformCube_average_residues A (fun z => if E z then 1 else 0)

/-- Exact CRT intersections on a fixed uniform interval cube, with their
complete finite boundary error. -/
theorem sieveCRT_cube_sample_discrepancy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i) × ZMod (∏ i, s i) × ZMod (∏ i, s i))
    (N : ℕ) [NeZero N]
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) :
    |(uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
        (fun j => ∀ i, E i (sieveCubeCRT s hcop
          (A.1 + (j.1.val : ZMod (∏ i, s i)),
            A.2.1 + (j.2.1.val : ZMod (∏ i, s i)),
            A.2.2 + (j.2.2.val : ZMod (∏ i, s i))) i)) -
      ∏ i, (uniformResidueCubeLaw (s i)).probability (E i)| ≤
      3 * (∏ i, s i : ℕ) / (N : ℝ) := by
  rw [uniformCube_probability_residues A (fun x => ∀ i, E i (sieveCubeCRT s hcop x i)),
    ← sieveCRT_cube_probability s hcop E]
  exact residueCube_probability_discrepancy A N (NeZero.pos N) _

lemma uniformInterval_probability_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D) (E : ZMod D → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (A + (j.val : ZMod D))) =
      (intervalResidueLaw A N (NeZero.pos N)).probability E := by
  unfold FiniteLaw.probability
  rw [uniformFiniteLaw_average, intervalResidueLaw_average_uniform]

lemma interval_probability_discrepancy {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (E : ZMod D → Prop) :
    |(intervalResidueLaw A N hN).probability E - (uniformZModLaw D).probability E| ≤
      (D : ℝ) / N := by
  have hd := finite_observable_difference (intervalResidueLaw A N hN).weight
    (uniformZModLaw D).weight (fun x => if E x then 1 else 0)
    (fun x => by split_ifs <;> norm_num)
  have hv := intervalResidueLaw_totalVariation A N hN
  change |(intervalResidueLaw A N hN).probability E -
    (uniformZModLaw D).probability E| ≤ _ at hd
  calc
    _ ≤ 2 * finiteTotalVariation (intervalResidueLaw A N hN).weight
        (uniformZModLaw D).weight := hd
    _ ≤ 2 * ((D : ℝ) / (2 * N)) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

theorem sieveCRT_one_sample_discrepancy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) :
    |(uniformFiniteLaw (Fin N)).probability
        (fun j => ∀ i, E i (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))) i)) -
      ∏ i, (uniformZModLaw (s i)).probability (E i)| ≤ (∏ i, s i : ℕ) / (N : ℝ) := by
  rw [uniformInterval_probability_residues A
    (fun x => ∀ i, E i (ZMod.prodEquivPi s hcop x i)), ← sieveCRT_one_probability s hcop E]
  exact interval_probability_discrepancy A N (NeZero.pos N) _

lemma sieveCubeCRT_natCast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (a b c : ℕ) (i : ι) :
    sieveCubeCRT s hcop (a, b, c) i =
      ((a : ZMod (s i)), (b : ZMod (s i)), (c : ZMod (s i))) := by
  simp [sieveCubeCRT, ZMod.prodEquivPi_apply,
    ZMod.cast_natCast (dvd_prod_of_mem s (mem_univ i))]

end TwoPointCorrelations

end OAI
