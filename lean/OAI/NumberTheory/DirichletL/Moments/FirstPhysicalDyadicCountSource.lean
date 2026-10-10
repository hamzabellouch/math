import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount
import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_frequency_radius_cap (I J:Ideal O)(E:Finset (CommonIndex I J))
    (K V Z B ξ:ℝ)(hK:0<K)(hV:0≤V)(hZ:1≤Z)
    (hVcap:V≤Z^B)(hKcap:K⁻¹≤Z^B):
    frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K V) Z ξ≤Z^(3*B+ξ/2) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hT:V^2/K≤Z^(3*B):=by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV hVcap 2) hKcap
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  unfold frequencyRadius
  calc
    _≤Z^(3*B)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      ((first_nominal_scale_le I J E K V hK).trans hT) (Real.rpow_nonneg hz.le _)
    _=_:=by rw [←Real.rpow_add hz]

theorem original_local_blocks_subpower (B Hcap ξ ε:ℝ)
    (hB:0≤B)(hHcap:0≤Hcap)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K V H:ℝ),
      0<K→0≤V→0<H→V≤Z^B→K⁻¹≤Z^B→H≤Z^Hcap→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K V) Z ξ)
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_blocks_subpower Hcap (3*B+ξ/2) 1 ε
    hHcap (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro C D hC hD E K V H hK hV hH hVcap hKcap hHbound
  exact hcount C D hC hD E K _ H hK hH
    (by simpa only [one_mul] using (local_frequency_radius_cap C D E K V Z B ξ
      hK hV hZ hVcap hKcap)) hHbound

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤hi i)(hb₁:|s.b₁|≤b₁)(hb₂:|s.b₂|≤b₂)
    (hZ:1≤Z)(hfixed:(∏i,hi i)*b₁*b₂≤Z)
    (hV:volume s.toData≤Z^B):sourceRadius s≤Z^(B+1) := by
  have hVol:0<volume s.toData:=volume_pos s.toData
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s.toData:=by
    unfold sourceRadius volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hhi i)
  have hb₁0:0≤b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

theorem original_input_local_blocks_subpower {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (volume s.toData)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_local_blocks_subpower B (B+1) ξ ε
    hB (by positivity) hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hcount hZ hfixed
  intro s hhi hb₁ hb₂ hH C D hC hD E K hK hV hKi
  exact hcount C D hC hD E K _ _ hK (volume_pos s.toData).le hH hV hKi
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)

lemma input_radius_pos_of_live {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hlive:coefficient s R seed I≠0):0<sourceRadius s := by
  obtain ⟨hI,hcap⟩:=original_column_norm s R seed I hz₁ hz₂ hlive
  exact (CenteredMomentFirstScale.norm_pos I hI).trans_le hcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
