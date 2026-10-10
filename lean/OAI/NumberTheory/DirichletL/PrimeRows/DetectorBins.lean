import OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

lemma detector_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e))
    (hpole : ¬((χ j).residue=1 ∧ s=1)) : LFunction (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e≤s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im|≤3*(i+1:ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  exact detector_nonzero_above_maximum χ _ j (hmax.trans_le hre) him hpole

lemma detectorEntire_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e)) :
    detectorEntire (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr
  have hre : 0<s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  intro hz
  obtain ⟨hL,hpole⟩ := (detectorEntire_zero_iff (χ j) hre).mp hz
  exact detector_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht hs hpole hL

lemma exists_detector_buffered_bin (χ : ι→Character)
    (T e : ℝ) (hT : 2<T) (he : 0<e) (n : ℕ) (hn : 0<n)
    (hwidth : (49/100:ℝ)≤n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a≤1 ∧ a≤detectorMaximum χ (3*i*T) ∧
      detectorMaximum χ (3*i*T)<a+e ∧
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (χ j) s=0 ∧ ¬((χ j).residue=1 ∧ s=1) ∧
        a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*i*T) ∧
      (∀j t,|t|≤(3*i+2:ℕ)*T → ∀s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e),
        detectorEntire (χ j) s≠0) := by
  let M : ℕ→ℝ := fun j=>detectorMaximum χ (3*(j+1:ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _=>detectorMaximum_bounds χ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,hpole,ht,hs⟩ := detectorMaximum_attained χ (3*(i+1:ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,hpole,by rw [hs];exact hlo,by rw [hs];exact hhi,ht⟩
  · intro j t ht s hs
    apply detectorEntire_nonzero_on_buffered_disk χ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α:=ℝ) k]) he hnext j t ht hs

lemma detectorMaximum_eq_nonprincipal (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ) :
    detectorMaximum χ T=HeckeDetectorZeros.zeroMaximum χ hχ T := by
  have hz (i : ι) : detectorZeroFinset (χ i) T=HeckeDetectorZeros.zeroFinset (χ i) (hχ i) T := by
    ext s
    simp [hχ i]
  have hr : detectorRealParts χ T=HeckeDetectorZeros.realParts χ hχ T := by
    simp only [detectorRealParts,HeckeDetectorZeros.realParts,detectorFamilyZeros,HeckeDetectorZeros.familyZeros,hz]
  unfold detectorMaximum HeckeDetectorZeros.zeroMaximum
  simp only [hr]

end SevenEighths.ProbeHighRowFamily

end

end OAI
