import OAI.Analysis.AncientFlat.Geometry.InteriorSchauder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem window_center_estimate (α κ K : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℝ), 0<q → q≤1 →
      ∀ (p0 : V × ℝ) (Ω : Set (V × ℝ)), MapsTo (window p0 q) (cylinder 2) Ω →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α Ω a K → HolderBound α Ω b K → (∀ p∈Ω, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈Ω, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α Ω u ut M) →
      HolderBound α Ω (fun p => f p.2 p.1) F → (∀ p∈Ω, ‖u p.2 p.1‖≤U) →
      (∀ p∈Ω, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      (∀ n : ℕ, n≤4 → ‖iteratedFDeriv ℝ n (u p0.2) p0.1‖≤(C/q^4)*(F+U)) ∧
      ‖ut p0.2 p0.1‖≤(C/q^4)*(F+U) := by
  obtain ⟨C,hC,Hlocal⟩ := interior_schauder (V := V) α κ K hα hα1 hκ hK
  refine ⟨C,hC,?_⟩
  intro q hq hq1 p0 Ω hm a b ha hb hell u ut f F U hF hU hs hd hj hf hu he
  obtain ⟨M,hM,hj⟩ := hj
  have Hloc := Hlocal (fun p => a (window p0 q p)) (fun p => q^4 • b (window p0 q p))
    (holder_window hα.le hq hq1 p0 ha hm) (holder_window_smul hα.le hK hq hq1 p0 4 hb hm)
    (fun p hp => hell _ (hm hp))
    (windowValue p0 q u) (windowTime p0 q ut) (windowTime p0 q f) F U hF hU
    (windowValue_contDiff p0 q u hs) (fun p hp => window_hasDerivAt p0 q u ut p (hd _ (hm hp)))
    ⟨M,hM,window_jet_bound hα.le hM hq hq1 p0 u ut hs hj hm⟩
    (holder_window_smul hα.le hF hq hq1 p0 4 hf hm) (fun p hp => hu _ (hm hp))
    (fun p hp => window_equation p0 q a b u ut f hs p (he _ (hm hp)))
  have hz : ((0:V),(0:ℝ))∈cylinder 1 := by norm_num [cylinder]
  have hq4 : 0<q^4 := pow_pos hq _
  constructor
  · intro n hn
    have hh := (Hloc.1 n hn).1 (0,0) hz
    dsimp only at hh
    rw [window_jet p0 q u hs n hn (0,0),window_zero,norm_smul,Real.norm_of_nonneg (pow_nonneg hq.le n)] at hh
    have hp : q^4≤q^n := pow_le_pow_of_le_one hq.le hq1 hn
    have hm := (mul_le_mul_of_nonneg_right hp (norm_nonneg (iteratedFDeriv ℝ n (u p0.2) p0.1))).trans hh
    have hhdiv : ‖iteratedFDeriv ℝ n (u p0.2) p0.1‖≤C*(F+U)/q^4 :=
      (le_div_iff₀ hq4).mpr (by simpa [mul_comm] using hm)
    convert hhdiv using 1; ring
  · have hh := Hloc.2.1 (0,0) hz
    simp only [windowTime,smul_zero,add_zero,mul_zero,norm_smul,Real.norm_of_nonneg hq4.le] at hh
    have hhdiv : ‖ut p0.2 p0.1‖≤C*(F+U)/q^4 :=
      (le_div_iff₀ hq4).mpr (by simpa [mul_comm] using hh)
    convert hhdiv using 1; ring

theorem nested_derivative_sup (α κ K : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (r R : ℝ), 1≤r → r<R → R≤2 →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α (cylinder R) a K → HolderBound α (cylinder R) b K → (∀ p∈cylinder R, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder R, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α (cylinder R) u ut M) →
      HolderBound α (cylinder R) (fun p => f p.2 p.1) F → (∀ p∈cylinder R, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder R, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      ∀ p∈cylinder r,
      (∀ n : ℕ, n≤4 → ‖iteratedFDeriv ℝ n (u p.2) p.1‖≤(C/(R-r)^4)*(F+U)) ∧
      ‖ut p.2 p.1‖≤(C/(R-r)^4)*(F+U) := by
  obtain ⟨C,hC,Hw⟩ := window_center_estimate (V := V) α κ K hα hα1 hκ hK
  refine ⟨256*C,by positivity,?_⟩
  intro r R hr hrR hR a b ha hb hell u ut f F U hF hU hs hd hj hf hu he p hp
  let q := (R-r)/4
  have hq : 0<q := by dsimp [q]; linarith
  have hq1 : q≤1 := by dsimp [q]; linarith
  have hm4 := small_window_maps (by linarith : 0≤r) hq (by dsimp [q]; linarith : 4*q≤R-r) p hp
  have hm : MapsTo (window p q) (cylinder 2) (cylinder R) :=
    fun z hz => hm4 (cylinder_mono (by norm_num) (by norm_num : (2:ℝ)≤4) hz)
  have hh := Hw q hq hq1 p (cylinder R) hm a b ha hb hell u ut f F U hF hU hs hd hj hf hu he
  have heq : C/q^4=256*C/(R-r)^4 := by dsimp [q]; field_simp; ring
  simpa only [heq] using hh
end ParabolicLocalization

end

end OAI
