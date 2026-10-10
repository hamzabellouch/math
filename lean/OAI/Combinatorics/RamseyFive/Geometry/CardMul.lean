import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Weight
import OAI.Combinatorics.RamseyFive.Geometry.ProjectiveLinePairPacking
import OAI.Combinatorics.RamseyFive.Probability.SamplingDegree
import OAI.Combinatorics.RamseyFive.Decoding.PairExpBound

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ProjectiveRichLines
open Module
open scoped LinearAlgebra.Projectivization Classical
open AffineRealization
variable {K L I ι J : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype I] [Fintype ι] [Nonempty ι] [Fintype J]

theorem card_mul_le {q : ℕ} [CharP L q] (h2 : (2:L) ≠ 0)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W)
    (M Kp h C : ℕ) (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) (hM2 : 2 ≤ M)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun i => (p i).rep ∈ W l)).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ U)).card ≤ Kp)
    (hprob : (Fintype.card J:ℝ)*Real.exp (-f*M/12) < 1/2)
    (hsize : 2*f*Fintype.card ι < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ f*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*Fintype.card ι) :
    Fintype.card J*M ≤ (6+72*C)*Fintype.card ι := by
  classical
  obtain ⟨a, ha, hr⟩ := exists_projective_realization (L := L) hI p hp
  obtain ⟨i, j, hij, hi, hj⟩ := exists_line_indices p W (fun l => hM2.trans (hM l))
  let S : Finset (Fin 3 → L) := Finset.univ.image a
  have hSc : S.card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ]
  have hSn : S.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hv : ∀ l, a (j l)-a (i l) ≠ 0 := by
    intro l he
    exact hij l (ha (sub_eq_zero.mp he).symm)
  have hlines : ∀ l, M ≤ (SharpLogRamsey.AffineIncidence.onLine
      (fun l => a (i l)) (fun l => a (j l)-a (i l)) S l).card := by
    intro l
    have hc := line_count_of_ranks p hp a ha hr (W l) (hW l) (hij l) (hi l) (hj l)
    exact (hM l).trans_eq hc
  have hcap' (P : MvPolynomial (Fin 3) L) (hP : P.totalDegree = 1) :
      (S.filter (fun y => MvPolynomial.eval y P = 0)).card ≤ Kp := by
    exact plane_cap_of_ranks (by omega) p a ha hr Kp hcap P hP
  have hd := distinct_lines_of_ranks p hp a hr W hW hWinj i j hij hi hj
  have H := SharpLogRamsey.RichAffineLines.card_mul_le h2 S hSn
    (fun l => a (i l)) (fun l => a (j l)-a (i l)) hv hd
    M Kp h C f hf hf1 hlines hcap' hprob (by rwa [hSc]) hdeg
    hchar hMD hKM (by rwa [hSc])
  rwa [hSc] at H

theorem quantitative_card_mul_le {q : ℕ} [CharP L q] (h2 : (2:L) ≠ 0)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun i => (p i).rep ∈ W l)).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ U)).card ≤ Kp)
    (hlarge : (1024:ℝ)^2*Fintype.card ι ≤ (M:ℝ)^3)
    (hchar : 51*Real.sqrt ((Fintype.card ι:ℝ)/M) < q)
    (hKM : 8*Kp ≤ M^2) :
    Fintype.card J*M ≤ 20814*Fintype.card ι := by
  obtain ⟨f,h,hf,hf1,hsize,hdeg,hcq,hMD,hD,hfe⟩ :=
    RichParameters.exists_sampling_degree (Fintype.card ι) M q (by omega) hMN hlarge hchar
  apply card_mul_le (L := L) h2 hI p hp W hW hWinj M Kp h 289 f hf hf1 hM2 hM hcap
    _ hsize hdeg hcq hMD hKM hD
  have hc := projective_line_pair_packing p hp W hW hWinj M hM
  have hu := RichParameters.pair_exp_bound hM2 hMN hc
  convert hu using 1
  congr 2
  rw [neg_mul, hfe]
  ring
end SharpRamseyFive.ProjectiveRichLines

end OAI
