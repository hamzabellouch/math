import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailSeed
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma paid_seed_power (Z Bseed saving seedNorm : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) :
    Z^(-(saving+Bseed))≤Z^(-saving)/seedNorm := by
  apply (le_div_iff₀ hs).mpr
  calc
    _≤Z^(-(saving+Bseed))*Z^Bseed :=
      mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by rw [←Real.rpow_add hZ];congr 1;ring

lemma paid_seed_term (Z Bseed saving seedNorm A : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) (hA : 0≤A) :
    A*Z^(-(saving+Bseed))≤A*Z^(-saving)/seedNorm := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (paid_seed_power Z Bseed saving seedNorm hZ hs hcap) hA

omit [DecidableEq ι] in
theorem second_input_tail_seed (hi : ι→ℝ) (wlo whi B Bseed ξ saving : ℝ)
    (hhi : ∀i,0≤hi i) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B) (hξ : 0<ξ) :
    ∃SΦ : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(s : Input ι)(W₁ W₂ : 𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),
      seed≠0→(seed.absNorm:ℝ)≤Z^Bseed→
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        Z^(-saving)/(seed.absNorm:ℝ) := by
  obtain ⟨SΦ,C,hC,hbound⟩ := second_input_tail_arbitrary_saving hi wlo whi B ξ
    (saving+Bseed) hhi hwlo hwhi hB hξ
  refine ⟨SΦ,C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hseed hseedcap hK hV hT hnom
  have hsn : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed)
  exact (hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hV hT hnom).trans
    (paid_seed_term Z Bseed saving (seed.absNorm:ℝ) _ (zero_lt_one.trans hz.1) hsn hseedcap
      (by positivity))

end SevenEighths.CenteredMomentSourceInputTailSeed

end

end OAI
