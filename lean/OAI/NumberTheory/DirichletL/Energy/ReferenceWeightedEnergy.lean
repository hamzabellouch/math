import OAI.NumberTheory.DirichletL.Energy.ReferenceSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceWeightedEnergy
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison
local notation "O"=>HeckeFamily.O

lemma finite_weighted_energy {ι κ:Type*}[Fintype ι][Fintype κ]
    (a f:ι→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤q j)
    (ha:∀i j,‖a i j‖≤ρ j)(E:ℝ)(hE:0≤E)
    (hf:∀j,∑i,‖f i j‖^2≤E*(q j)^2):
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j*q j)^2*E:=by
  have hb(j:κ):(∑i,‖a i j*f i j‖^2)≤(ρ j*q j*Real.sqrt E)^2:=by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2:=Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2):=(Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*(E*(q j)^2):=mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_:=by rw [mul_pow,Real.sq_sqrt hE];ring
  have hh:=CompletedGauss.finite_tsum_energy_bound (fun j i=>a i j*f i j)
    (fun j=>ρ j*q j*Real.sqrt E) (fun j=>mul_nonneg (mul_nonneg (hρ j) (hq j)) (Real.sqrt_nonneg E))
    (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

theorem radial_weighted_energy {κ:Type*}[Fintype κ]
    (a f:O→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤q j)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K E:ℝ)
    (hΦ:∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (ha:∀z,keep z→∀j,‖a z j‖≤ρ j)(hE:0≤E)
    (hs:∀j,Summable (fun z:O=>if keep z then ‖f z j‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0))
    (hf:∀j,radialEnergy (fun z=>f z j) keep Φ K≤E*(q j)^2):
    radialEnergy (fun z=>∑j,a z j*f z j) keep Φ K≤(∑j,ρ j*q j)^2*E:=by
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let w(z:S):ℂ:=(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=finite_weighted_energy (fun z:S=>a z) (fun z:S=>fun j=>f z j*w z) ρ q hρ hq
    (fun z=>ha z (Finset.mem_filter.mp z.property).2) E hE ?_
  · have hsum(z:S):(∑j,a z j*(f z j*w z))=(∑j,a z j*f z j)*w z:=by
      rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro j _;ring
    simp_rw [hsum] at hh
    dsimp only [w] at hh
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>∑j,a z j*f z j) Φ K hΦ] at hh
    exact hh
  · intro j
    dsimp only [w]
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>f z j) Φ K hΦ]
    exact ((hs j).sum_le_tsum rows (fun z _=>by
      split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans (hf j)

end SevenEighths.CenteredMomentEnergyReferenceWeightedEnergy

end

end OAI
