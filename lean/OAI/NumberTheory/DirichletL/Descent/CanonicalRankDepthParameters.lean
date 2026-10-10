import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData
import OAI.NumberTheory.DirichletL.Descent.RecursionParameters

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_rank_depth_covers (Mmax cutoff:ℝ)(hcut:0<cutoff):
    Mmax≤rankRowCap (actualDepth Mmax (cutoff/2)) cutoff := by
  have hceil:=Nat.le_ceil (2*Mmax/(3*(cutoff/2)))
  have hscaled:2*Mmax≤(⌈2*Mmax/(3*(cutoff/2))⌉₊:ℝ)*(3*(cutoff/2)):=
    (div_le_iff₀ (by positivity:0<3*(cutoff/2))).mp hceil
  unfold rankRowCap actualDepth
  push_cast
  nlinarith

theorem actual_rank_depth_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤c/200 ∧ eta≤c/100000 ∧
      let n:=actualDepth Mmax (cutoff/2);
      0<n ∧ Mmax≤rankRowCap n cutoff ∧
      ∀k:ℕ,k≤n→Fmax≤rankTotalCap k (Fmax+1) eta ∧
        c/2≤rankMargin k c eta ∧ rankMargin k c eta≤c ∧
        0≤rankLoss k eta ∧ rankLoss k eta≤eps/4 := by
  let csmall:=min c 1
  have hcs:0<csmall:=lt_min hc (by norm_num)
  have hcc:csmall≤c:=min_le_left _ _
  have hc1:csmall≤1:=min_le_right _ _
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutc,hetac,hbudgets⟩:=
    actual_recursion_parameters Mmax Fmax csmall eps hM hF hcs heps
  dsimp only at hbudgets
  refine ⟨cutoff,eta,hcut,heta,heta1,hetacut,by linarith,by linarith,by linarith,?_⟩
  dsimp only
  refine ⟨actualDepth_pos _ _,actual_rank_depth_covers Mmax cutoff hcut,?_⟩
  intro k hk
  have hk':(k:ℝ)≤(actualDepth Mmax (cutoff/2):ℝ):=by exact_mod_cast hk
  have hmono:=mul_le_mul_of_nonneg_right hk' heta.le
  have hk0:0≤(k:ℝ):=Nat.cast_nonneg _
  have hkE:0≤(k:ℝ)*eta:=mul_nonneg hk0 heta.le
  rcases hbudgets with ⟨hmargin,hsize,hloss⟩
  unfold rankTotalCap rankMargin rankLoss
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem actual_rank_top_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃(n:ℕ)(cutoff eta:ℝ),n=actualDepth Mmax (cutoff/2) ∧
      0<n ∧ 0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤c/200 ∧ eta≤c/100000 ∧
      Mmax≤rankRowCap n cutoff ∧ Fmax≤rankTotalCap n (Fmax+1) eta ∧
      c/2≤rankMargin n c eta ∧ rankMargin n c eta≤c ∧
      0≤rankLoss n eta ∧ rankLoss n eta<eps := by
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutL,hcutc,hetac,hn,hrow,hall⟩:=
    actual_rank_depth_parameters Mmax Fmax c eps hM hF hc heps
  have htop:=hall (actualDepth Mmax (cutoff/2)) le_rfl
  refine ⟨actualDepth Mmax (cutoff/2),cutoff,eta,rfl,hn,hcut,heta,heta1,hetacut,
    hcutL,hcutc,hetac,hrow,htop.1,htop.2.1,htop.2.2.1,htop.2.2.2.1,?_⟩
  linarith [htop.2.2.2.2]

end SevenEighths.InverseMoment

end

end OAI
