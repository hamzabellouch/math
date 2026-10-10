import OAI.NumberTheory.Jacobsthal.Paths.ActualTagFreezing

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeTraceInvariance
open FinitePathGeometry PrimeHistories RepresentativeAdmission SourceStopPredicate

theorem terminal_side_length (w : ℝ) (z z' : Node) (ps qs : List ℕ)
    (hz : z.side = z'.side) (hlen : ps.length = qs.length) :
    (terminal w z ps).side = (terminal w z' qs).side := by
  induction ps generalizing qs z z' with
  | nil =>
    have hq : qs = [] := List.length_eq_zero_iff.mp hlen.symm
    subst qs
    exact hz
  | cons p ps ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      apply ih (step w z p) (step w z' q) qs
      · change z.side.flip = z'.side.flip
        rw [hz]
      · simpa using hlen

theorem representative_last_eq (rep : ℕ → ℝ) (ps qs : List ℕ)
    (hm : ps.map rep = qs.map rep) : rep (ps.getLastD 0) = rep (qs.getLastD 0) := by
  induction ps generalizing qs with
  | nil =>
    have hq : qs = [] := List.map_eq_nil_iff.mp hm.symm
    subst qs
    rfl
  | cons p ps ih =>
    cases qs with
    | nil => simp at hm
    | cons q qs =>
      have hh := List.cons.inj hm
      cases ps with
      | nil =>
        have hq : qs = [] := List.map_eq_nil_iff.mp hh.2.symm
        subst qs
        exact hh.1
      | cons r rs =>
        cases qs with
        | nil => simp at hh
        | cons s ss =>
          simpa using ih (s::ss) hh.2

theorem representativeWindow_map_iff (rep : ℕ → ℝ) (z : Node) (b₀ b₁ : ℝ)
    (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) :
    representativeWindow rep z b₀ b₁ ps ↔ representativeWindow rep z b₀ b₁ qs := by
  have he := representative_last_eq rep ps qs hm
  simp only [representativeWindow,representativeGap,he,hm]

theorem representativeSafe_map_iff (w : ℝ) (rep : ℕ → ℝ) (z : Node) (Delta : ℝ)
    (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) :
    representativeSafe w rep z Delta ps ↔ representativeSafe w rep z Delta qs := by
  have forward (ps qs : List ℕ) (hm : ps.map rep = qs.map rep)
      (hs : representativeSafe w rep z Delta ps) : representativeSafe w rep z Delta qs := by
    intro pre hpre hne hside
    obtain ⟨tail,htail⟩ := (List.mem_inits pre qs).mp hpre
    have hlen : ps.length = qs.length := by simpa using congrArg List.length hm
    have hk : pre.length ≤ ps.length := by rw [← htail,List.length_append] at hlen; omega
    have hm' : (ps.take pre.length).map rep = pre.map rep := by
      rw [List.map_take,hm,← htail,List.map_append,List.take_append]
      simp
    have hprefix : ps.take pre.length ∈ ps.inits :=
      (List.mem_inits _ _).mpr ⟨ps.drop pre.length,List.take_append_drop _ _⟩
    have hlen' : (ps.take pre.length).length = pre.length := by
      rw [List.length_take,Nat.min_eq_left hk]
    have hne' : ps.take pre.length ≠ [] := by
      intro he
      have : pre.length = 0 := by rw [he] at hlen'; simpa using hlen'.symm
      exact hne (List.length_eq_zero_iff.mp this)
    have hside' : (terminal w z (ps.take pre.length)).side = .even :=
      (terminal_side_length w z z _ _ rfl hlen').trans hside
    have hh := hs (ps.take pre.length) hprefix hne' hside'
    have he := representative_last_eq rep _ _ hm'
    simpa only [representativeGap,hm',he] using hh
  exact ⟨forward ps qs hm,forward qs ps hm.symm⟩

theorem all_prefix_representative_tests (w : ℝ) (rep : ℕ → ℝ) (z : Node)
    (Delta b₀ b₁ : ℝ) (ps qs : List ℕ) (hm : ps.map rep = qs.map rep) (k : ℕ) :
    (representativeSafe w rep z Delta (ps.take k) ↔ representativeSafe w rep z Delta (qs.take k)) ∧
    (representativeWindow rep z b₀ b₁ (ps.take k) ↔ representativeWindow rep z b₀ b₁ (qs.take k)) := by
  have ht : (ps.take k).map rep = (qs.take k).map rep := by rw [List.map_take,List.map_take,hm]
  exact ⟨representativeSafe_map_iff w rep z Delta _ _ ht,
    representativeWindow_map_iff rep z b₀ b₁ _ _ ht⟩
end NumberTheoryLean.RepresentativeTraceInvariance

end

section

namespace NumberTheoryLean.SourceCandidateFreezing
open FinitePathGeometry PrimeHistories RepresentativeAdmission SourceStopPredicate
open ActualSourceTags ActualTagFreezing FiniteFirstTag RepresentativeTraceInvariance
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem forall_take_replacement_iff (A : ℕ → Prop) (pre tail : List ℕ) (p p' : ℕ)
    (hp : A p) (hp' : A p') (k : ℕ) :
    (∀ r ∈ (pre++p::tail).take k,A r) ↔ (∀ r ∈ (pre++p'::tail).take k,A r) := by
  have hm : ((pre++p::tail).take k).map A = ((pre++p'::tail).take k).map A := by
    rw [List.map_take,List.map_take]
    have he : A p = A p' := propext (iff_of_true hp hp')
    simp only [List.map_append,List.map_cons,he]
  have forward (ps qs : List ℕ) (hm : ps.map A = qs.map A)
      (hh : ∀ r ∈ ps,A r) : ∀ r ∈ qs,A r := by
    intro r hr
    have hm' : A r ∈ ps.map A := by rw [hm]; exact List.mem_map.mpr ⟨r,hr,rfl⟩
    obtain ⟨s,hs,he⟩ := List.mem_map.mp hm'
    rw [← he]
    exact hh s hs
  exact ⟨forward _ _ hm,forward _ _ hm.symm⟩

theorem prefix_tag_eq {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ) (k : ℕ)
    {t u : Tag n} (ht : firstTag F ps = some t) (hu : firstTag F (ps.take k) = some u) : u=t := by
  have hh := firstTagFrom_append F 0 (ps.take k) (ps.drop k) hu
  rw [List.take_append_drop] at hh
  exact Option.some.inj (hh.symm.trans ht)

theorem all_prefix_candidate_replacement {n : ℕ} (Y : ℕ) (w Cs eta Clen B xi b₀ b₁ : ℝ)
    (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℕ) (z : Node)
    (pre tail : List ℕ) (p p' : ℕ) {t : Tag n}
    (ht : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p::tail) = some t)
    (hc : tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a) p = some (t.bin,t.rational))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns (sourceClass a) t.rational p') (k : ℕ) :
    stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ((pre++p::tail).take k) ↔
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ((pre++p'::tail).take k) := by
  have hwit := candidate_witness (Y:ℝ) w Cs eta lower width label (sourceClass a) p hc
  have hp := hwit.2.1
  have ha := hwit.2.2.2.2
  have htags := all_prefix_tags_replacement (Y:ℝ) w Cs eta lower width label (sourceClass a)
    pre tail p p' hc hlabel hp' ha' k
  have hfull := sourceTag_replacement (Y:ℝ) w Cs eta lower width label (sourceClass a)
    pre tail p p' hc hlabel hp' ha'
  have ht' : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) (pre++p'::tail) = some t :=
    hfull.symm.trans ht
  have hlabels : ((pre++p::tail).take k).map label = ((pre++p'::tail).take k).map label := by
    rw [List.map_take,List.map_take,replacement_labels label pre tail p p' hlabel]
  have hrep := all_prefix_representative_tests w (representative w lower width label) z
    (2*Clen*xi) b₀ b₁ _ _ (replacement_representatives w lower width label pre tail p p' hlabel) k
  have hboxed := forall_take_replacement_iff
    (fun r => r ∈ primeBin (lower (label r)) (width (label r))) pre tail p p' hp hp' k
  have halign := forall_take_replacement_iff (aligns (sourceClass a) t.rational) pre tail p p' ha ha' k
  have hlen : ((pre++p::tail).take k).length = ((pre++p'::tail).take k).length := by
    simp only [List.length_take,List.length_append,List.length_cons]
  have hne : ((pre++p::tail).take k ≠ []) ↔ ((pre++p'::tail).take k ≠ []) := by
    rw [← List.length_pos_iff,← List.length_pos_iff,hlen]
  have forward (ps qs : List ℕ)
      (hps : firstTag (tagCandidate (Y:ℝ) w Cs eta lower width label (sourceClass a))
        ((pre++p::tail).take k) = sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps)
      (htag : sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) ps =
        sourceTag (Y:ℝ) w Cs eta lower width label (sourceClass a) qs)
      (hne : ps ≠ [] → qs ≠ []) (hlen : ps.length = qs.length)
      (hb : boxed lower width label ps → boxed lower width label qs)
      (hs : representativeSafe w (representative w lower width label) z (2*Clen*xi) ps →
        representativeSafe w (representative w lower width label) z (2*Clen*xi) qs)
      (hw : representativeWindow (representative w lower width label) z b₀ b₁ ps →
        representativeWindow (representative w lower width label) z b₀ b₁ qs)
      (hl : ps.map label = qs.map label)
      (ha : (∀ r ∈ ps,aligns (sourceClass a) t.rational r) → ∀ r ∈ qs,aligns (sourceClass a) t.rational r)
      (H : stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z ps) :
      stopCandidate Y w Cs eta Clen B xi b₀ b₁ lower width label a z qs := by
    obtain ⟨hn,hlength,hbox,hsafe,hwindow,u,hu,hcount,hal⟩ := H
    have hu' := hps.trans hu
    have hut : u=t := prefix_tag_eq _ (pre++p::tail) k ht hu'
    subst u
    exact ⟨hne hn,by simpa only [← hlen] using hlength,hb hbox,hs hsafe,hw hwindow,
      t,htag.symm.trans hu,by simpa only [← hl] using hcount,ha hal⟩
  exact ⟨forward _ _ rfl htags hne.mp hlen hboxed.mp hrep.1.mp hrep.2.mp hlabels halign.mp,
    forward _ _ htags htags.symm hne.mpr hlen.symm hboxed.mpr hrep.1.mpr hrep.2.mpr hlabels.symm halign.mpr⟩
end NumberTheoryLean.SourceCandidateFreezing

end

end Erdos970

end OAI
