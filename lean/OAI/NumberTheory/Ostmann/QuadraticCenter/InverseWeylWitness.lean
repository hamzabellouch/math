import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitnessAbel
import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitnessAmplitude
import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitnessLength

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem centered_quadratic_witness_inverse {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i,NeZero (p i)] [NeZero (∏ i,p i)]
    (hp : ∀ i,(p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i,Finset (ZMod (p i))) (mInv : ZMod (∏ i,p i))
    (s v : ℕ) (R h θ : ℝ) :
    let d := ∏ i,p i
    let N := Real.sqrt (R/((s:ℝ)*v/(d:ℕ)))
    let Y := N/d
    ∀ ε B : ℝ, (d:ℝ) ≤ N → 0 < ε → ε ≤ 1 → 1 ≤ B →
      B ≤ Y*(ε/(10*cutoffFourierBound)) →
      1024*(1+Real.log (2*Y)) ≤ (ε/(10*cutoffFourierBound))^2*B →
      Real.sqrt ((2:ℝ)^Fintype.card ι)*ε ≤
        ‖centeredQuadraticSum p hcop S mInv s v 1 R h θ‖ →
      ∃ q : ℕ,1 ≤ q ∧ (q:ℝ) ≤ 2*B ∧
        integerDistance ((q:ℝ)*((h+θ)*((s:ℝ)*v*d))) ≤
          B/(Y*(ε/(10*cutoffFourierBound)))^2 := by
  let d := ∏ i,p i
  let N := Real.sqrt (R/((s:ℝ)*v/(d:ℕ)))
  let Y := N/d
  let α := (h+θ)*((s:ℝ)*v/d)
  change ∀ ε B : ℝ, (d:ℝ) ≤ N → 0 < ε → ε ≤ 1 → 1 ≤ B →
      B ≤ Y*(ε/(10*cutoffFourierBound)) →
      1024*(1+Real.log (2*Y)) ≤ (ε/(10*cutoffFourierBound))^2*B →
      Real.sqrt ((2:ℝ)^Fintype.card ι)*ε ≤
        ‖centeredQuadraticSum p hcop S mInv s v 1 R h θ‖ → _
  intro ε B hdN hε hε1 hB hBsmall hscale hlarge
  have hd : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_neZero d
  have hN : 0 < N := hd.trans_le hdN
  have hY : 1 ≤ Y := (le_div_iff₀ hd).mpr (by simpa using hdN)
  obtain ⟨r,hr⟩ := centered_quadratic_witness_progression p hp hcop S mInv s v R h θ ε hN hlarge
  let J := witnessBlockCount d N
  have hJ : (J:ℝ) ≤ Y+1 := (witnessBlockCount_bounds hN).2
  have hx : (0:ℝ) ≤ (r.val:ℝ)+1 := by positivity
  have hxd : (r.val:ℝ)+1 ≤ d := by exact_mod_cast r.isLt
  have hweighted : (N/(d:ℝ))*ε ≤ ‖∑ j ∈ Finset.range J,
      weylPhase (α*((r.val:ℝ)+1+(d:ℝ)*(j:ℝ))^2)*
        progressionCutoffWeight N d ((r.val:ℝ)+1) j‖ := by
    simpa only [witnessProgression,progressionCutoffWeight,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
      using hr
  obtain ⟨n,hn,hnorm,hnlo⟩ := exists_quadraticWeylSum_of_weighted_progression
    hN hd hdN hx hxd J hJ hweighted
  have hC : 1 ≤ cutoffFourierBound := by
    have h0 := cutoffSeminorm_nonneg 0
    have h1 := cutoffSeminorm_nonneg 1
    unfold cutoffFourierBound
    linarith
  let η := ε/(10*cutoffFourierBound)
  have hη : 0 < η := div_pos hε (by positivity)
  have hη2 : η ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 10*cutoffFourierBound)).mpr
    linarith
  have hnup : (n:ℝ) ≤ 2*Y := by
    have hh : (n:ℝ) ≤ J := by exact_mod_cast hn
    linarith
  have hh := inverse_weyl_at_witness_scale (α*(d:ℝ)^2)
    (2*α*d*((r.val:ℝ)+1)) Y η B n hY hη hη2 hB hBsmall hscale hnup
    (by simpa only [η,Y,mul_div_assoc] using hnorm)
    (by simpa only [η,Y,mul_div_assoc] using hnlo)
  have hphase : α*(d:ℝ)^2 = (h+θ)*((s:ℝ)*v*d) := by
    dsimp [α]
    field_simp
  simpa only [hphase] using hh

end Ostmann.QuadraticCenter

end

end OAI
