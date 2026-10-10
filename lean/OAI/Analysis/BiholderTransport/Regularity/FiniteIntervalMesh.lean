import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.UniformFiniteRadialScale

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport

lemma finite_interval_mesh {K ε e : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (he : e∈Ioo (0:ℝ) 1) :
    ∃ N : ℕ, 0<N ∧ ∃ t : ℕ → ℝ, t 0=0 ∧ t N=1-e ∧
      (∀ k≤N, t k∈Icc (0:ℝ) (1-e)) ∧
      ∀ k<N, K*|t (k+1)-t k| ≤ ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (K/ε+1)
  have hn0 : (0:ℝ)<N := by
    have := div_nonneg hK hε.le
    linarith
  have hNnat : 0<N := by exact_mod_cast hn0
  let t : ℕ → ℝ := fun k => (k:ℝ)/N*(1-e)
  refine ⟨N,hNnat,t,by simp [t],by simp [t,ne_of_gt hn0],?_,?_⟩
  · intro k hk
    have hr : (k:ℝ)/N ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hk)
    have hr0 : 0 ≤ (k:ℝ)/N := div_nonneg (Nat.cast_nonneg _) hn0.le
    dsimp [t]
    constructor
    · exact mul_nonneg hr0 (by linarith [he.2])
    · have HH := mul_le_mul_of_nonneg_right hr (show 0 ≤ 1-e by linarith [he.2])
      simpa only [one_mul] using HH
  · intro k hk
    have hstep : t (k+1)-t k=(1-e)/N := by
      dsimp [t]
      rw [Nat.cast_add,Nat.cast_one]
      ring
    rw [hstep,abs_of_nonneg (div_nonneg (by linarith [he.2]) hn0.le)]
    have hKN : K/N ≤ ε := by
      rw [div_le_iff₀ hn0]
      have HH := (div_lt_iff₀ hε).mp (show K/ε<(N:ℝ) by linarith [hN])
      linarith
    have HH := mul_le_mul_of_nonneg_left (show (1-e)/N ≤ 1/N by
      exact div_le_div_of_nonneg_right (by linarith [he.1]) hn0.le) hK
    rw [mul_one_div] at HH
    exact HH.trans hKN
end WeakMTWTransport

end

end

section

noncomputable section
open Set

namespace WeakMTWTransport

lemma uniform_finite_profile_comparison {C l u b D e K : ℝ}
    (hC : 0<C) (hl : 0<l) (hu : 0<u) (hb : 0<b) (hD : 0<D)
    (he : e∈Ioo (0:ℝ) 1) (heC : e*C ≤ l/32) (hK : 0 ≤ K) :
    ∃ c : ℝ, 0<c ∧ ∀ (s : ℝ → ℝ) (f : ℝ → ℝ → ℝ),
      (∀ t∈Icc (0:ℝ) 1, 0 ≤ s t) → s 1 ≤ D →
      (∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (0:ℝ) 1,
        l*δ/(s t+δ)-b*δ ≤ f δ t ∧ f δ t ≤ u*δ/(s t+δ)+b*δ) →
      (∀ δ∈Ioc (0:ℝ) (1/2), ∀ x∈Icc (0:ℝ) (1-e), ∀ y∈Icc (0:ℝ) (1-e),
        |f δ y-f δ x| ≤ K*|y-x|) →
      (∀ δ∈Ioc (0:ℝ) (1/2), f δ (1-e) ≤ (1-e)*f δ 1+e*C) →
      c*s 1 ≤ s 0 := by
  classical
  let ε := l/16
  have hε : 0<ε := by
    dsimp [ε]
    linarith only [heC, mul_pos he.1 hC]
  obtain ⟨N,hN,t,ht0,htN,ht,hstep⟩ := finite_interval_mesh hK hε he
  let L := 32*u/l+1
  have hL : 0<L := by dsimp [L]; positivity
  have hR : 1 ≤ Real.exp L := (show 1 ≤ L+1 by linarith).trans (Real.add_one_le_exp L)
  have hRu : u/Real.exp L ≤ l/32 := by
    rw [div_le_iff₀ (Real.exp_pos L)]
    have HH := Real.add_one_le_exp L
    have HH2 := mul_le_mul_of_nonneg_left HH hl.le
    have hcancel : l*(32*u/l)=32*u := by field_simp
    dsimp [L] at HH2
    nlinarith only [HH2,hcancel,hl]
  let η := min (1/2:ℝ) (l/(32*b))
  have hη : 0<η := lt_min (by norm_num) (div_pos hl (by positivity))
  obtain ⟨c,hc,HC⟩ := uniform_finite_radial_scale (N := N+1) hD hη hL
  refine ⟨c,hc,?_⟩
  intro s f hs hsD hprof hlip hend
  by_contra H
  have hfail : s 0<c*s 1 := lt_of_not_ge H
  have hs₀ := hs 0 (by constructor <;> norm_num)
  have hs₁ : 0<s 1 := by nlinarith only [hfail,hs₀,hc]
  let S := (Finset.range (N+1)).image (fun k => s (t k))
  have hSc : S.card ≤ N+1 := Finset.card_image_le.trans (by simp)
  obtain ⟨δ,hd0,hdη,hdsmall,hdlarge,hdsep⟩ := HC S hSc (s 0) (s 1) hs₁ hsD hfail
  have hd : δ∈Ioc (0:ℝ) (1/2) := ⟨hd0,hdη.trans (min_le_left _ _)⟩
  have hbg : b*δ ≤ l/32 := by
    have HH := hdη.trans (min_le_right _ _)
    have HH2 := (le_div_iff₀ (show 0<32*b by positivity)).mp HH
    nlinarith only [HH2]
  have hti (k : ℕ) (hk : k≤N) : t k∈Icc (0:ℝ) 1 :=
    ⟨(ht k hk).1,le_trans (ht k hk).2 (by linarith [he.1])⟩
  have hlarge_case (r : ℝ) (hr : r∈Icc (0:ℝ) 1) (hh : Real.exp L*s r ≤ δ) :
      l/4 ≤ f δ r := by
    have HH := radial_profile_small (hs r hr) hd0 hl.le hR hh hbg (hprof δ hd r hr).1
    linarith
  have hsmall_case (r : ℝ) (hr : r∈Icc (0:ℝ) 1) (hh : δ*Real.exp L ≤ s r) :
      f δ r ≤ ε := by
    have HH := radial_profile_large (hs r hr) hd0 hu.le (Real.exp_pos L) hh hbg
      (hprof δ hd r hr).2
    dsimp [ε]
    linarith
  have hfzero : l/4 ≤ f δ (t 0) := by
    rw [ht0]
    exact hlarge_case 0 (by constructor <;> norm_num) hdsmall
  have hfend : f δ 1 ≤ ε := hsmall_case 1 (by constructor <;> norm_num) hdlarge
  have hfbin (k : ℕ) (hk : k≤N) : f δ (t k) ≤ ε ∨ l/4 ≤ f δ (t k) := by
    have hmem : s (t k)∈S := Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩
    rcases hdsep _ hmem with Hs|Hs
    · exact Or.inr (hlarge_case (t k) (hti k hk) Hs)
    · exact Or.inl (hsmall_case (t k) (hti k hk) Hs)
  have hfstep (k : ℕ) (hk : k<N) : |f δ (t (k+1))-f δ (t k)| ≤ ε :=
    (hlip δ hd (t k) (ht k (by omega)) (t (k+1)) (ht (k+1) (by omega))).trans (hstep k hk)
  have Hlarge := finite_spectral_gap_propagation (f := fun k => f δ (t k))
    (show 2*ε<l/4 by dsimp [ε]; linarith) hfbin hfstep hfzero
  rw [htN] at Hlarge
  have Hup := hend δ hd
  have HH := mul_le_mul_of_nonneg_left hfend (show 0 ≤ 1-e by linarith [he.2])
  have HH2 := mul_nonneg hε.le he.1.le
  dsimp [ε] at HH HH2
  nlinarith only [Hlarge,Hup,HH,HH2,heC,hl]
end WeakMTWTransport

end

end

end

end OAI
