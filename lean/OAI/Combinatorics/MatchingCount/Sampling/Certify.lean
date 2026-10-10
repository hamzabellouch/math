import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.RelationDestinations
import OAI.Combinatorics.MatchingCount.Tapes.RunBits

namespace OAI

namespace MatchingFPRAS.Counting

lemma sigma_nonneg (D K : ℕ) (epsilon : ℚ) (he : 0 ≤ epsilon) : 0  ≤  sigma D K epsilon := by
  unfold sigma alpha; positivity

lemma sigma_small (D K : ℕ) (hD : 1 ≤ D) (epsilon : ℚ) : sigma D K epsilon  ≤  (1:ℚ)/10000000 := by
  have hDr : (1:ℚ) ≤ D := by exact_mod_cast hD
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (by positivity : 0  <  (100:ℚ)*D)).mpr
  norm_num [alpha]
  linarith

lemma sigma_times_D (D K : ℕ) (hD : 1 ≤ D) (epsilon : ℚ) : (D:ℚ)*sigma D K epsilon  ≤  alpha/100 := by
  have hDr : (1:ℚ) ≤ D := by exact_mod_cast hD
  have hs : sigma D K epsilon  ≤  alpha/(100*D) := min_le_left _ _
  have hm := (le_div_iff₀ (by positivity : 0  <  (100:ℚ)*D)).mp hs
  norm_num [alpha] at hm ⊢
  nlinarith only [hm]

lemma sigma_relative (D K : ℕ) (epsilon : ℚ) : 10*sigma D K epsilon  ≤  epsilon/(100*K) := by
  have h : sigma D K epsilon  ≤  epsilon/(1000*K) := min_le_right _ _
  calc
    _  ≤  10*(epsilon/(1000*K)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

lemma ratio_error (s a d abar dbar : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ (1:ℚ)/100)
    (ha : (1:ℚ)/2 ≤ a) (hR : (1:ℚ)/2 ≤ d/a  ∧  d/a ≤ 1)
    (haerr : |abar-a| ≤ s) (hderr : |dbar-d| ≤ s) :
    |ratioEstimate abar dbar/(d/a)-1|  ≤  10*s := by
  have hab := abs_le.mp haerr
  have hdb := abs_le.mp hderr
  have hap : 0 < a := by linarith
  have habp : 0 < abar := by linarith
  have hRp : 0 < d/a := by linarith [hR.1]
  have hden : (1:ℚ)/5  ≤  (d/a)*abar := by
    have hbar : (1:ℚ)/2-s  ≤  abar := by linarith
    have hm := mul_le_mul hR.1 hbar (by linarith : 0  ≤  (1:ℚ)/2-s) hRp.le
    nlinarith
  have hnum : |dbar-(d/a)*abar|  ≤  2*s := by
    have hid : dbar-(d/a)*abar=(dbar-d)+(d/a)*(a-abar) := by
      have hm : (d/a)*a=d := div_mul_cancel₀ d hap.ne'
      nlinarith
    rw [hid]
    calc
      _  ≤  |dbar-d|+|(d/a)*(a-abar)| := abs_add_le _ _
      _ = |dbar-d|+(d/a)*|abar-a| := by rw [abs_mul,abs_of_pos hRp,abs_sub_comm a abar]
      _  ≤  s+(d/a)*s := add_le_add hderr (mul_le_mul_of_nonneg_left haerr hRp.le)
      _  ≤  2*s := by nlinarith [mul_le_mul_of_nonneg_right hR.2 hs]
  have hid : ratioEstimate abar dbar/(d/a)-1=(dbar-(d/a)*abar)/((d/a)*abar) := by
    simp only [ratioEstimate, ite_eq_left habp]
    have hdne : d ≠ 0 := by intro hh; simp [hh] at hRp
    field_simp [hap.ne', habp.ne', hdne]
  rw [hid,abs_div,abs_of_pos (mul_pos hRp habp)]
  apply (div_le_iff₀ (mul_pos hRp habp)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hden (show 0 ≤ 10*s by positivity)]



lemma upper_error (D : ℕ) (hD : 1 ≤ D) (s d z dbar zbar : ℚ)
    (hs : 0 ≤ s) (hs1 : s ≤ (1:ℚ)/100)
    (hDs : (D:ℚ)*s ≤ alpha/100) (hd : (1:ℚ)/4 ≤ d)
    (hg : 0 ≤ (D:ℚ)*z/d ∧ (D:ℚ)*z/d ≤ 2)
    (hderr : |dbar-d| ≤ s) (hzerr : |zbar-z| ≤ s) :
    alpha ≤ upperEstimate D dbar zbar ∧ upperEstimate D dbar zbar ≤ 3 ∧
    (D:ℚ)*z/d ≤ upperEstimate D dbar zbar ∧
    upperEstimate D dbar zbar ≤ (D:ℚ)*z/d+2*alpha := by
  have hDr : (1:ℚ) ≤ D := by exact_mod_cast hD
  have hdp : 0 < d := by linarith
  have hdb := abs_le.mp hderr
  have hbar : (1:ℚ)/5 ≤ dbar := by linarith
  have hbarp : 0 < dbar := by linarith
  let g := (D:ℚ)*z/d
  have hg0 : 0 ≤ g := hg.1
  have hg2 : g ≤ 2 := hg.2
  have hnum : |(D:ℚ)*(zbar-z)+g*(d-dbar)| ≤ ((D:ℚ)+2)*s := by
    calc
      _ ≤ |(D:ℚ)*(zbar-z)|+|g*(d-dbar)| := abs_add_le _ _
      _ = (D:ℚ)*|zbar-z|+g*|dbar-d| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), abs_of_nonneg hg0,
          abs_sub_comm d dbar]
      _ ≤ (D:ℚ)*s+g*s := add_le_add (mul_le_mul_of_nonneg_left hzerr (Nat.cast_nonneg D))
        (mul_le_mul_of_nonneg_left hderr hg0)
      _ ≤ ((D:ℚ)+2)*s := by nlinarith [mul_le_mul_of_nonneg_right hg2 hs]
  have hid : (D:ℚ)*zbar/dbar-g=((D:ℚ)*(zbar-z)+g*(d-dbar))/dbar := by
    dsimp [g]
    field_simp [hdp.ne', hbarp.ne']
    ring
  have hraw : |(D:ℚ)*zbar/dbar-g| ≤ alpha := by
    rw [hid, abs_div, abs_of_pos hbarp]
    apply (div_le_iff₀ hbarp).mpr
    have hsm : s ≤ (D:ℚ)*s := by nlinarith [mul_le_mul_of_nonneg_right hDr hs]
    have ha : 0 < alpha := by norm_num [alpha]
    have hm := mul_le_mul_of_nonneg_left hbar ha.le
    norm_num [alpha] at hDs hm ⊢
    nlinarith only [hDs, hm, hnum, hsm]
  have hbounds := abs_le.mp hraw
  unfold upperEstimate
  rw [ite_eq_left hbarp]
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · apply max_le
    · norm_num [alpha]
    · exact min_le_left _ _
  · apply le_max_of_le_right
    exact le_min (by linarith) (by linarith)
  · apply max_le
    · have ha : 0 ≤ alpha := by norm_num [alpha]
      linarith
    · exact (min_le_right _ _).trans (by linarith)



theorem successful_stage_estimates (D K : ℕ) (hD : 1 ≤ D) (_hK : 1 ≤ K)
    (epsilon : ℚ) (he : 0<epsilon) (he1 : epsilon<1)
    (a d z abar dbar zbar : ℚ) (ha : (1:ℚ)/2 ≤ a) (hd : (1:ℚ)/4 ≤ d)
    (hR : (1:ℚ)/2 ≤ d/a ∧ d/a ≤ 1)
    (hg : 0 ≤ (D:ℚ)*z/d ∧ (D:ℚ)*z/d ≤ 2)
    (haerr : |abar-a| ≤ sigma D K epsilon)
    (hderr : |dbar-d| ≤ sigma D K epsilon)
    (hzerr : |zbar-z| ≤ sigma D K epsilon) :
    0<abar ∧ 0<dbar ∧
    |ratioEstimate abar dbar/(d/a)-1| ≤ 10*sigma D K epsilon ∧
    10*sigma D K epsilon ≤ epsilon/(100*K) ∧
    alpha ≤ upperEstimate D dbar zbar ∧ upperEstimate D dbar zbar ≤ 3 ∧
    (D:ℚ)*z/d ≤ upperEstimate D dbar zbar ∧
    upperEstimate D dbar zbar ≤ (D:ℚ)*z/d+2*alpha := by
  have hs := sigma_nonneg D K epsilon he.le
  have hs1 : sigma D K epsilon ≤ (1:ℚ)/100 :=
    (sigma_small D K hD epsilon).trans (by norm_num)
  have hab := abs_le.mp haerr
  have hdb := abs_le.mp hderr
  refine ⟨by linarith, by linarith, ?_, sigma_relative D K epsilon, ?_⟩
  · exact ratio_error _ _ _ _ _ hs hs1 ha hR haerr hderr
  · exact upper_error D hD _ _ _ _ _ hs hs1 (sigma_times_D D K hD epsilon) hd hg hderr hzerr

end MatchingFPRAS.Counting

namespace MatchingFPRAS.Transport.Sparse

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

instance decideMatching (M : Finset E) :
    Decidable (MatchingOn (fun e v => v ∈ ends e) M univ) := by
  unfold MatchingOn ExistsUnique
  infer_instance

def certify (s : Finset (Finset E)) : Finset (PM (fun e v => v ∈ ends e)) :=
  Finset.subtype (fun A => MatchingOn (fun e v => v ∈ ends e) A univ) s

@[simp] lemma mem_certify (s : Finset (Finset E)) (A : PM (fun e v => v ∈ ends e)) :
    A ∈ certify ends s ↔ A.val ∈ s := Finset.mem_subtype

lemma card_certify (s : Finset (Finset E)) : (certify ends s).card ≤ s.card := by
  simpa only [certify,card_subtype] using
    card_filter_le s (fun A => MatchingOn (fun e v => v ∈ ends e) A univ)

def colorRaw (A : Finset E) : Finset (Finset E) :=
  A.biUnion fun e => (univ.filter (fun f => ends f = ends e)).image
    (fun f => insert f (A.erase e))

def colors (A : PM (fun e v => v ∈ ends e)) : Finset (PM (fun e v => v ∈ ends e)) :=
  certify ends (colorRaw ends A.val)

omit [Fintype V] in
@[simp] lemma mem_colorRaw [Fintype V] (A B : Finset E) :
    B ∈ colorRaw ends A ↔ ∃ e ∈ A, ∃ f, ends f = ends e ∧ B = insert f (A.erase e) := by
  simp only [colorRaw,mem_biUnion,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨e,he,f,hf,h⟩
    exact ⟨e,he,f,hf,h.symm⟩
  · rintro ⟨e,he,f,hf,h⟩
    exact ⟨e,he,f,hf,h.symm⟩

@[simp] lemma mem_colors (A B : PM (fun e v => v ∈ ends e)) :
    B ∈ colors ends A ↔ ColorChange ends A B := by
  rw [colors,mem_certify,mem_colorRaw]
  constructor
  · rintro ⟨e,he,f,hf,hB⟩
    refine ⟨e,f,A.val.erase e,hf.symm,?_,?_⟩
    · simpa only [union_singleton] using (insert_erase he).symm
    · simpa only [union_singleton] using hB
  · exact ColorChange.edit ends

lemma colors_eq (A : PM (fun e v => v ∈ ends e)) :
    colors ends A = colorDestinations ends A := by
  ext B
  simp [colorDestinations]

omit [Fintype V] in
lemma colorRaw_card [Fintype V] (A : Finset E) :
    (colorRaw ends A).card ≤ A.card * Fintype.card E := by
  calc
    _ ≤ ∑ e ∈ A, ((univ.filter (fun f => ends f = ends e)).image
          (fun f => insert f (A.erase e))).card := card_biUnion_le
    _ ≤ ∑ _e ∈ A, Fintype.card E := sum_le_sum fun e _ =>
      card_image_le.trans (card_le_univ _)
    _ = _ := by simp

def switchPatterns (A : Finset E) : Finset ((Fin 4 → V) × (Fin 4 → E)) :=
  univ.filter fun p => Function.Injective p.1 ∧
    (∀ i x, x ∈ ends (p.2 i) ↔ x = p.1 i ∨ x = p.1 (i+1)) ∧
    p.2 0 ≠ p.2 2 ∧ {p.2 0,p.2 2} ⊆ A

def switchRaw (A : Finset E) : Finset (Finset E) :=
  (switchPatterns ends A).image fun p => (A \ {p.2 0,p.2 2}) ∪ {p.2 1,p.2 3}

def switches (A : PM (fun e v => v ∈ ends e)) : Finset (PM (fun e v => v ∈ ends e)) :=
  certify ends (switchRaw ends A.val)

@[simp] lemma mem_switches (A B : PM (fun e v => v ∈ ends e)) :
    B ∈ switches ends A ↔ TwoEdgeSwitch A B := by
  rw [switches,mem_certify]
  constructor
  · intro h
    obtain ⟨⟨v,e⟩,hp,hB⟩ := mem_image.mp h
    obtain ⟨hv,he,hne,hsub⟩ := (mem_filter.mp hp).2
    refine ⟨v,e,A.val \ {e 0,e 2},hv,he,?_,hB.symm⟩
    exact (sdiff_union_of_subset hsub).symm
  · intro h
    obtain ⟨v,e,hv,he,hne,hsub,hB⟩ := h.normal_form
    exact mem_image.mpr ⟨(v,e),mem_filter.mpr ⟨mem_univ _,hv,he,hne,hsub⟩,hB.symm⟩

lemma switches_eq (A : PM (fun e v => v ∈ ends e)) :
    switches ends A = switchDestinations A := by
  ext B
  simp [switchDestinations]

lemma switchRaw_card (A : Finset E) :
    (switchRaw ends A).card ≤ (Fintype.card V)^4*(Fintype.card E)^4 := by
  calc
    _ ≤ (switchPatterns ends A).card := card_image_le
    _ ≤ Fintype.card ((Fin 4 → V) × (Fin 4 → E)) := card_le_univ _
    _ = _ := by simp

theorem colors_card (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : (colors ends A).card ≤ 2*A.val.card := by
  rw [colors_eq]
  exact colorDestinations_card_bound ends hpar A

theorem switches_card (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) : (switches ends A).card ≤ 8*A.val.card.choose 2 := by
  rw [switches_eq]
  exact switchDestinations_card_bound ends hpar A

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS.ComputableReach

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (G : SimpleGraph α) [DecidableRel G.Adj]

def grow (s : Finset α) : Finset α := s ∪ univ.filter (fun b => ∃ a ∈ s, G.Adj a b)

def reached (s : Finset α) (n : ℕ) : Finset α := (grow G)^[n] s

def closure (a : α) : Finset α := reached G {a} (Fintype.card α)

lemma mem_grow (s : Finset α) (b : α) :
    b ∈ grow G s ↔ b ∈ s ∨ ∃ a ∈ s, G.Adj a b := by simp [grow]

lemma subset_grow (s : Finset α) : s ⊆ grow G s := subset_union_left

lemma grow_mono : Monotone (grow G) := by
  intro s t h b hb
  rcases (mem_grow G s b).mp hb with hb | ⟨a,ha,hab⟩
  · exact (mem_grow G t b).mpr (Or.inl (h hb))
  · exact (mem_grow G t b).mpr (Or.inr ⟨a,h ha,hab⟩)

lemma reached_step (s : Finset α) (n : ℕ) : reached G s (n+1) = grow G (reached G s n) :=
  Function.iterate_succ_apply' _ _ _

lemma reached_step' (s : Finset α) (n : ℕ) : reached G s (n+1) = reached G (grow G s) n :=
  Function.iterate_succ_apply _ _ _

lemma reached_succ (s : Finset α) (n : ℕ) : reached G s n ⊆ reached G s (n+1) := by
  rw [reached_step]
  exact subset_grow G _

lemma reached_mono_time (s : Finset α) : Monotone (reached G s) :=
  monotone_nat_of_le_succ (reached_succ G s)

lemma reached_reachable (a b : α) (n : ℕ) (h : b ∈ reached G {a} n) : G.Reachable a b := by
  induction n generalizing b with
  | zero =>
    have hb : b=a := by simpa [reached] using h
    subst b
    exact SimpleGraph.Reachable.refl a
  | succ n ih =>
    rw [reached_step,mem_grow] at h
    rcases h with h | ⟨c,hc,hcb⟩
    · exact ih b h
    · exact (ih c hc).trans hcb.reachable

lemma walk_reached {s : Finset α} {a b : α} (p : G.Walk a b) (ha : a ∈ s) :
    b ∈ reached G s p.length := by
  induction p generalizing s with
  | nil => exact ha
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.length_cons,reached_step']
    exact ih ((mem_grow G s b).mpr (Or.inr ⟨a,ha,hab⟩))

@[simp] theorem mem_closure (a b : α) : b ∈ closure G a ↔ G.Reachable a b := by
  constructor
  · exact reached_reachable G a b _
  · rintro ⟨p⟩
    exact reached_mono_time G {a} p.toPath.isPath.length_lt.le
      (walk_reached G p.toPath.val (mem_singleton_self a))

def cellsWritten : ℕ := (Fintype.card α+1)*Fintype.card α

omit [DecidableEq α] in
lemma cellsWritten_bound [DecidableEq α] : cellsWritten (α:=α) ≤ (Fintype.card α+1)^2 := by
  unfold cellsWritten
  nlinarith

end MatchingFPRAS.ComputableReach

end OAI
