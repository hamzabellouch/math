import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactFiberDecomposition

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma compactFiberMarginal_abs_bound {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} {M : ℝ} (h : ∀ p,|f p|≤M) (x : E) :
    |compactFiberMarginal a b f x|≤(b-a)*M := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun t => f (x,t)) (C := M)
    (fun t _ => by simpa only [Real.norm_eq_abs] using h (x,t))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm,
    compactFiberMarginal] using hh

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma fiberPrimitive_abs_bound {a b : ℝ} (hab : a≤b)
    {f : E×ℝ → ℝ} (hf : Continuous f)
    (hv : ∀ p,f p≠0 → p.2∈Ioo a b)
    (hz : ∀ x,(∫ t in a..b,f (x,t))=0)
    {M : ℝ} (hM : 0≤M) (h : ∀ p,|f p|≤M) (p : E×ℝ) :
    |fiberPrimitive a f p|≤(b-a)*M := by
  by_cases ha : p.2≤a
  · rw [fiberPrimitive_below hf hv p ha,abs_zero]
    positivity
  by_cases hb : b≤p.2
  · rw [fiberPrimitive_above hf hv hz p hb,abs_zero]
    positivity
  rw [fiberPrimitive_eq_integral a hf]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := p.2) (f := fun t => f (p.1,t)) (C := M)
    (fun t _ => by simpa only [Real.norm_eq_abs] using h (p.1,t))
  rw [Real.norm_eq_abs,abs_of_pos (sub_pos.mpr (lt_of_not_ge ha))] at hh
  exact hh.trans (by nlinarith [lt_of_not_ge hb])

theorem compact_fiber_decomposition_bounded {a b : ℝ} (hab : a<b)
    {f : E×ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hs : HasCompactSupport f) (hv : ∀ p,f p≠0 → p.2∈Ioo a b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hsη : HasCompactSupport η)
    (hvη : tsupport η⊆Ioo a b) (hiη : (∫ t in a..b,η t)=1)
    {M K : ℝ} (hM : 0≤M) (hK : 0≤K)
    (hbound : ∀ p,|f p|≤M) (hηbound : ∀ t,|η t|≤K) :
    ∃ F : E×ℝ → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) F ∧ HasCompactSupport F ∧
      (∀ p,wallDerivative F p+η p.2*compactFiberMarginal a b f p.1=f p) ∧
      tsupport F⊆(Prod.fst '' tsupport f) ×ˢ Icc a b ∧
      (∀ p,|F p|≤(b-a)*(1+K*(b-a))*M) ∧
      (∀ p,|wallDerivative F p|≤(1+K*(b-a))*M) ∧
      F=fiberPrimitive a (fun p => f p-η p.2*compactFiberMarginal a b f p.1) := by
  let R := compactFiberMarginal a b f
  have hR := compactFiberMarginal_smooth hab.le hf
  have hsR : HasCompactSupport R := (compactFiberMarginal_support (a := a) (b := b) hs).1
  let g := fun p : E×ℝ => f p-η p.2*R p.1
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.sub ((hη.comp contDiff_snd).mul (hR.comp contDiff_fst))
  have hsg : HasCompactSupport g := by
    apply hs.sub
    apply HasCompactSupport.of_support_subset_isCompact (hsR.prod hsη)
    intro p hp
    exact ⟨subset_tsupport R (mul_ne_zero_iff.mp hp).2,subset_tsupport η (mul_ne_zero_iff.mp hp).1⟩
  have hvg : ∀ p,g p≠0 → p.2∈Ioo a b := by
    intro p hp
    by_contra hn
    have hz : f p=0 := by by_contra hh; exact hn (hv p hh)
    have hzη : η p.2=0 := image_eq_zero_of_notMem_tsupport (fun hh => hn (hvη hh))
    exact hp (by simp [g,hz,hzη])
  have hzg : ∀ x,(∫ t in a..b,g (x,t))=0 := by
    intro x
    rw [show (fun t => g (x,t))=(fun t => f (x,t)-η t*R x) from rfl,
      intervalIntegral.integral_sub (f := fun t => f (x,t)) (g := fun t => η t*R x)
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
        ((hη.continuous.mul continuous_const).intervalIntegrable a b)]
    rw [intervalIntegral.integral_mul_const,hiη,one_mul]
    exact sub_self _
  have hgb (p : E×ℝ) : |g p|≤(1+K*(b-a))*M := by
    calc
      |g p| ≤ |f p|+|η p.2| * |R p.1| := by simpa only [g,abs_mul] using abs_sub (f p) (η p.2*R p.1)
      _ ≤ M+K*((b-a)*M) := add_le_add (hbound p)
        (mul_le_mul (hηbound p.2) (compactFiberMarginal_abs_bound hab.le hbound p.1) (abs_nonneg _) hK)
      _ = _ := by ring
  have hc := fiberPrimitive_compact hg.continuous hsg hvg hzg
  refine ⟨fiberPrimitive a g,fiberPrimitive_smooth a hg,hc.1,?_,?_,?_,?_,rfl⟩
  · intro p
    rw [fiberPrimitive_derivative a hg]
    exact sub_add_cancel _ _
  · apply hc.2.trans
    intro p hp
    refine ⟨?_,hp.2⟩
    obtain ⟨q,hq,hqp⟩ := hp.1
    by_contra hn
    have hfg : Function.support g⊆(Prod.fst '' tsupport f) ×ˢ univ := by
      intro y hy
      refine ⟨?_,mem_univ _⟩
      by_contra hyf
      have hz : f y=0 := by
        by_contra h
        exact hyf ⟨y,subset_tsupport f h,rfl⟩
      have hzR : R y.1=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hyf ((compactFiberMarginal_support hs).2 h))
      exact hy (by simp [g,hz,hzR])
    have hts := closure_minimal hfg ((hs.image continuous_fst).isClosed.prod isClosed_univ)
    exact hn (hqp ▸ (hts hq).1)
  · intro p
    simpa only [mul_assoc] using fiberPrimitive_abs_bound hab.le hg.continuous hvg hzg
      (by positivity : 0≤(1+K*(b-a))*M) hgb p
  · intro p
    rw [fiberPrimitive_derivative a hg]
    exact hgb p

end ScalarConductivity

end

end OAI
