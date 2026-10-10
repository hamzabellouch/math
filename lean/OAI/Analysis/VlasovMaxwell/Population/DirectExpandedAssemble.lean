import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalDirectTransportDensity
import OAI.Analysis.VlasovMaxwell.Population.SharedBudget
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedDeficitUniform
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedLargeAngular

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma ennreal_sum_subset_bound {α : Type*} {s t : Finset α} {f g : α→ℝ≥0∞}
    (hst : s⊆t) (hfg : ∀x∈s,f x≤g x) : (∑x∈s,f x)≤∑x∈t,g x :=
  (Finset.sum_le_sum hfg).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _=>bot_le))

lemma ennreal_radius_split (f : ℕ→ℝ≥0∞) (r : ℕ→ℝ) (I : ℝ) :
    (∑'n,f n)≤(∑'n,if r n≤I then f n else 0)+(∑'n,if I≤r n then f n else 0) := by
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases h : r n≤I
  · simp only [ite_eq_left h]
    exact le_add_right le_rfl
  · simp [h,(not_le.mp h).le]

lemma Admissible.direct_remaining_source_complete_uniform {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P K : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      I≤(w/P)^2 → 0≤K → (N:ℝ)≤K*Real.log (2+P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
      let Sf := (Finset.range N).filter (fun nf=>1/(32*w)≤cappedRepresentative nf)
      let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
      let Ss := fun nt=>(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt)
      (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr : ℕ,
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
          ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b))≤
      ENNReal.ofReal (C*(1+K^4)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Ch,hCh,hhigh⟩ := hd.direct_remaining_source_short_uniform_expanded
  obtain ⟨Cl,hCl,hlow⟩ := hd.direct_remaining_source_deficit_short_uniform_expanded
  obtain ⟨Cb,hCb,hlarge⟩ := hd.direct_remaining_source_large_uniform_expanded
  refine ⟨Ch+Cl+Cb,by positivity,?_⟩
  intro s T F hs hT zX S a b I w M A P K N hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP hIP hK hN HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
  let f := fun np nf nt j nr=>∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
    ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b)
  let r := fun nr=>max 1 T*cappedRepresentative nr
  let D := fun np nf nt j=>∑'nr,if r nr≤I then f np nf nt j nr else 0
  let L := fun np nf nt j=>∑'nr,if I≤r nr then f np nf nt j nr else 0
  let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
  let Sf := (Finset.range N).filter (fun nf=>1/(32*w)≤cappedRepresentative nf)
  let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
  let Ss := fun nt=>(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt)
  let hi := fun np j=>512≤cappedRepresentative j*sourceRepresentative np ∧ 32≤cappedRepresentative j*w
  let lo := fun np j=>cappedRepresentative j*sourceRepresentative np≤512 ∨ cappedRepresentative j*w≤32
  let Sh := fun np nt=>(Ss nt).filter (fun j=>hi np j)
  let R := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hR : P*Real.sqrt I≤R := le_add_of_nonneg_right (by positivity)
  have hR0 : 0≤R := by dsimp [R]; positivity
  have hp (np : ℕ) (hnp : np∈Sp) : sourceRepresentative np≤128*P := (Finset.mem_filter.mp hnp).2
  have hf (nf : ℕ) (hnf : nf∈Sf) : 1/(32*w)≤cappedRepresentative nf := (Finset.mem_filter.mp hnf).2
  have ht (nf nt : ℕ) (hnt : nt∈St nf) : cappedRepresentative nf≤16384*cappedRepresentative nt := (Finset.mem_filter.mp hnt).2
  have hj (nt j : ℕ) (hj : j∈Ss nt) : cappedRepresentative j≤131080*cappedRepresentative nt := (Finset.mem_filter.mp hj).2
  have hhigh' := hhigh s T F hs hT zX S a b I w M A P hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP HX HZ
    Sp Sf (fun _ nf=>St nf) (fun np _ nt=>Sh np nt) hp hf (fun _ _ nf _ nt hnt=>ht nf nt hnt)
    (fun np _ _ _ nt _ j hj'=>⟨hj nt j (Finset.mem_filter.mp hj').1,(Finset.mem_filter.mp hj').2⟩)
  have hlarge' := hlarge s T F hs hT zX S a b I w P hS hS0 ha hb hJI hI hI1 (by positivity)
    Sp Sf (fun _ nf=>St nf) (fun _ _ nt=>Ss nt) hp (fun _ _ nf _ nt hnt=>ht nf nt hnt)
    (fun _ _ _ _ nt _ j hj'=>hj nt j hj')
  have hlow' := hlow s T F hs hT zX S a b I w P K N hS hS0 ha hb hJI hI hI1 hw hP hIP hK hN
  have hlo : (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,if lo np j then D np nf nt j else 0)≤
      ENNReal.ofReal (Cl*K^4*(P*Real.sqrt I)) := by
    apply le_trans _ hlow'
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro np hnp
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro nf hnf
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro nt hnt
    apply ennreal_sum_subset_bound (Finset.filter_subset _ _)
    intro j hj'
    simp only [hp np hnp,ht nf nt hnt,true_and]
    exact le_rfl
  have hpoint (np nf nt j : ℕ) : (∑'nr,f np nf nt j nr)≤
      (if hi np j then D np nf nt j else 0)+(if lo np j then D np nf nt j else 0)+L np nf nt j := by
    apply (ennreal_radius_split (f np nf nt j) r I).trans
    apply add_le_add _ le_rfl
    by_cases hl : lo np j
    · simp only [ite_eq_left hl]
      exact le_add_left le_rfl
    · have hh : hi np j := by
        dsimp [lo] at hl
        push Not at hl
        exact ⟨hl.1.le,hl.2.le⟩
      simp only [ite_eq_left hh,ite_eq_right hl,add_zero]
      exact le_rfl
  change (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr,f np nf nt j nr)≤_
  calc
    _≤∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,
        ((if hi np j then D np nf nt j else 0)+(if lo np j then D np nf nt j else 0)+L np nf nt j) :=
      Finset.sum_le_sum (fun np _=>Finset.sum_le_sum (fun nf _=>Finset.sum_le_sum
        (fun nt _=>Finset.sum_le_sum (fun j _=>hpoint np nf nt j))))
    _=(∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Sh np nt,D np nf nt j)+
        (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,if lo np j then D np nf nt j else 0)+
        (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,L np nf nt j) := by
      simp only [Sh,Finset.sum_filter,Finset.sum_add_distrib]
    _≤ENNReal.ofReal (Ch*R)+ENNReal.ofReal (Cl*K^4*(P*Real.sqrt I))+ENNReal.ofReal (Cb*(P*Real.sqrt I)) :=
      add_le_add (add_le_add hhigh' hlo) hlarge'
    _≤ENNReal.ofReal (Ch*R+Cl*K^4*R+Cb*R) := by
      rw [ENNReal.ofReal_add (by positivity : 0≤Ch*R+Cl*K^4*R) (by positivity),
        ENNReal.ofReal_add (by positivity : 0≤Ch*R) (by positivity)]
      exact add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hR (by positivity))))
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hR hCb))
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : Ch+Cl*K^4+Cb≤(Ch+Cl+Cb)*(1+K^4) := by
        nlinarith [mul_nonneg hCh (pow_nonneg hK 4),mul_nonneg hCb (pow_nonneg hK 4)]
      calc
        _=(Ch+Cl*K^4+Cb)*R := by ring
        _≤_ := mul_le_mul_of_nonneg_right hc hR0

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma ennreal_sum_filter_eq {α : Type*} (s : Finset α) (p : α→Prop) [DecidablePred p]
    (f : α→ℝ≥0∞) (hz : ∀x∈s,¬p x→f x=0) : (∑x∈s,f x)=∑x∈s.filter p,f x := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : p x
  · simp only [ite_eq_left hp]
  · simp only [ite_eq_right hp,hz x hx hp]

lemma Admissible.direct_remaining_source_unrestricted_uniform {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P K : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      I≤(w/P)^2 → 0≤K → (N:ℝ)≤K*Real.log (2+P) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
      let Sf := Finset.range N
      let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
      let Ss := fun _ : ℕ=>Finset.range N
      (∑np∈Sp,∑nf∈Sf,∑nt∈St nf,∑j∈Ss nt,∑'nr : ℕ,
        ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
          ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b))≤
      ENNReal.ofReal (C*(1+K^4)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨C,hC,hcomplete⟩ := hd.direct_remaining_source_complete_uniform
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX S a b I w M A P K N hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP hIP hK hN HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := fun np nf nt j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
  let G := fun np nf nt j=>∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
    ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b)
  let Sp := (Finset.range N).filter (fun np=>sourceRepresentative np≤128*P)
  let St := fun nf=>(Finset.range N).filter (fun nt=>cappedRepresentative nf≤16384*cappedRepresentative nt)
  have hV : Measurable V :=
    ((F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hzero (np nf nt j : ℕ) (hθ : cappedRepresentative nf≤16384*cappedRepresentative nt)
      (hbad : ¬(1/(32*w)≤cappedRepresentative nf ∧ cappedRepresentative j≤131080*cappedRepresentative nt)) :
      G np nf nt j=0 := by
    have hz (nr : ℕ) : (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nf nt j nr) z
        ∂physicalBinMeasure V (B np nf nt j nr) (Icc a b))=0 :=
      physicalDirectSource_integral_expanded_bad_zero s hV measurableSet_Icc hw hθ hbad
    simp only [G,hz,tsum_zero]
  have hh := hcomplete s T F hs hT zX S a b I w M A P K N hS hS0 ha hb hab hI hI1 hJI
    hM hA hP hL hw hwP hIP hK hN HX HZ
  apply le_trans _ hh
  change (∑np∈Sp,∑nf∈Finset.range N,∑nt∈St nf,∑j∈Finset.range N,G np nf nt j)≤
    ∑np∈Sp,∑nf∈(Finset.range N).filter (fun nf=>1/(32*w)≤cappedRepresentative nf),
      ∑nt∈St nf,∑j∈(Finset.range N).filter (fun j=>cappedRepresentative j≤131080*cappedRepresentative nt),G np nf nt j
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro np hnp
  calc
    _=(∑nf∈(Finset.range N).filter (fun nf=>1/(32*w)≤cappedRepresentative nf),
        ∑nt∈St nf,∑j∈Finset.range N,G np nf nt j) := by
      apply ennreal_sum_filter_eq
      intro nf hnf hbad
      apply Finset.sum_eq_zero
      intro nt hnt
      apply Finset.sum_eq_zero
      intro j hj
      exact hzero np nf nt j (Finset.mem_filter.mp hnt).2 (fun h=>hbad h.1)
    _=_ := by
      apply Finset.sum_congr rfl
      intro nf hnf
      apply Finset.sum_congr rfl
      intro nt hnt
      apply ennreal_sum_filter_eq
      intro j hj hbad
      exact hzero np nf nt j (Finset.mem_filter.mp hnt).2 (fun h=>hbad h.2)

end RVM

end

end OAI
