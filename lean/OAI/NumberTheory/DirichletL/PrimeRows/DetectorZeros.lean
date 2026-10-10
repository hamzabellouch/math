import OAI.NumberTheory.DirichletL.PrimeRows.BufferedContour
import OAI.NumberTheory.DirichletL.Hecke.DetectorZeros

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

def detectorEntire (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue=1 then HeckeOrigin.poleRemoved χ s else HeckeOrigin.continued χ s

lemma detectorEntire_eq_nonprincipal (χ : Character) (hχ : χ.residue≠1) :
    detectorEntire χ=LFunction χ := by
  funext s
  simp only [detectorEntire,HeckeOrigin.continued,ite_eq_right hχ]

lemma detectorEntire_entire (χ : Character) : Differentiable ℂ (detectorEntire χ) := by
  by_cases hχ : χ.residue=1
  · have he : detectorEntire χ=HeckeOrigin.poleRemoved χ := by funext s;simp [detectorEntire,hχ]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    exact LFunction_entire_nonprincipal χ hχ

lemma detectorEntire_zero_iff (χ : Character) {s : ℂ} (hs : 0<s.re) :
    detectorEntire χ s=0 ↔ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · simp only [detectorEntire,ite_eq_left hχ]
    by_cases h1 : s=1
    · subst s
      simp [HeckeOrigin.poleRemoved_one_ne_zero χ hχ,hχ]
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
      simp [mul_eq_zero,sub_ne_zero.mpr h1,h1]
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    simp [hχ]

lemma detectorEntire_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1<s.re) :
    detectorEntire χ s≠0 := by
  intro hz
  exact LFunction_ne_zero_of_one_lt_re χ hs ((detectorEntire_zero_iff χ (by linarith)).mp hz).1

def detectorZeros (χ : Character) (T : ℝ) : Set ℂ :=
  {s | s∈HeckeDetectorZeros.rectangle T ∧ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1)}

lemma detectorZeros_finite (χ : Character) (T : ℝ) : (detectorZeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (detectorEntire χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (detectorEntire_entire χ)
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (detectorEntire_ne_zero_of_one_lt_re χ (by norm_num : 1<(2:ℂ).re))
    (Set.mem_univ (2:ℂ)) isConnected_univ
  have hf := (HeckeDetectorZeros.rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (HeckeDetectorZeros.rectangle T)) hc)
  convert hf using 1
  ext s
  by_cases hs : s∈HeckeDetectorZeros.rectangle T
  · have hr : 0<s.re := by have h:=hs.1;linarith
    simp [detectorZeros,hs,detectorEntire_zero_iff χ hr]
  · simp [detectorZeros,hs]

def detectorZeroFinset (χ : Character) (T : ℝ) : Finset ℂ := (detectorZeros_finite χ T).toFinset

@[simp] lemma mem_detectorZeroFinset (χ : Character) (T : ℝ) (s : ℂ) :
    s∈detectorZeroFinset χ T ↔ (51/100:ℝ)≤s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  simp only [detectorZeroFinset,Set.Finite.mem_toFinset,detectorZeros,HeckeDetectorZeros.rectangle,Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def detectorFamilyZeros (χ : ι→Character) (T : ℝ) : Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i=>(detectorZeroFinset (χ i) T).image (fun s=>(i,s)))

@[simp] lemma mem_detectorFamilyZeros (χ : ι→Character) (T : ℝ) (i : ι) (s : ℂ) :
    (i,s)∈detectorFamilyZeros χ T ↔ (51/100:ℝ)≤s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) := by
  simp [detectorFamilyZeros]

def detectorRealParts (χ : ι→Character) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((detectorFamilyZeros χ T).image (fun p=>p.2.re))

lemma detectorRealParts_nonempty (χ : ι→Character) (T : ℝ) : (detectorRealParts χ T).Nonempty :=
  Finset.insert_nonempty _ _

def detectorMaximum (χ : ι→Character) (T : ℝ) : ℝ :=
  (detectorRealParts χ T).max' (detectorRealParts_nonempty χ T)

lemma detectorMaximum_mem (χ : ι→Character) (T : ℝ) : detectorMaximum χ T∈detectorRealParts χ T :=
  Finset.max'_mem _ _

lemma detectorMaximum_bounds (χ : ι→Character) (T : ℝ) :
    (51/100:ℝ)≤detectorMaximum χ T ∧ detectorMaximum χ T≤1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · norm_num
    · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_detectorFamilyZeros χ T i s |>.mp hs).2.1

lemma detector_zero_re_le_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : (51/100:ℝ)≤s.re) (ht : |s.im|≤T) (hz : LFunction (χ i) s=0)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : s.re≤detectorMaximum χ T := by
  have hle : s.re≤1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s),(mem_detectorFamilyZeros χ T i s).mpr ⟨hs,hle,ht,hz,hpole⟩,rfl⟩)

lemma detectorMaximum_attained (χ : ι→Character) (T : ℝ)
    (hmax : (51/100:ℝ)<detectorMaximum χ T) :
    ∃i s,LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) ∧
      |s.im|≤T ∧ s.re=detectorMaximum χ T := by
  have hm := detectorMaximum_mem χ T
  rcases Finset.mem_insert.mp hm with hm|hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩,hs,heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_detectorFamilyZeros χ T i s).mp hs
    exact ⟨i,s,hz.2.2.2.1,hz.2.2.2.2,hz.2.2.1,heq⟩

lemma detectorMaximum_mono (χ : ι→Character) {T T' : ℝ} (hT : T≤T') :
    detectorMaximum χ T≤detectorMaximum χ T' := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum χ T) with hm|hm
  · obtain ⟨i,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained χ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum χ T' i (by rw [heq];exact hm.le) (ht.trans hT) hz hpole
  · exact hm.trans (detectorMaximum_bounds χ T').1

lemma detector_nonzero_above_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : LFunction (χ i) s≠0 := by
  intro hz
  exact (not_lt_of_ge (detector_zero_re_le_maximum χ T i
    ((detectorMaximum_bounds χ T).1.trans hs.le) ht hz hpole)) hs

lemma detector_reciprocal_differentiableAt (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal (χ i)) s := by
  apply reciprocal_differentiableAt_of_nonzero (χ i) s
    (by intro h;have hb:=(detectorMaximum_bounds χ T).1;norm_num [h] at hs;linarith)
  exact detector_nonzero_above_maximum χ T i hs ht

end SevenEighths.ProbeHighRowFamily

end

end OAI
