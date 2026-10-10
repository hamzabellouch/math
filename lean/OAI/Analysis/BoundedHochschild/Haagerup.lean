import Mathlib
import OAI.Analysis.BoundedHochschild.MomentNorms

namespace OAI

/-! Free-group convolution bounds and transfer of Haagerup estimates to tracial algebras. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildLength
open Finset FreeGroup
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Word (α : Type*) := List (α × Bool)
def words : ℕ → Finset (Word α)
  | 0 => {[]}
  | n+1 => ((univ : Finset (α × Bool)) ×ˢ words n).image (fun p => p.1 :: p.2)
@[simp] lemma mem_words {w : Word α} {n : ℕ} : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a l => simp [words, ih]
def wordBall (N : ℕ) : Finset (Word α) := (range (N+1)).biUnion words
@[simp] lemma mem_wordBall {w : Word α} {N : ℕ} : w ∈ wordBall N ↔ w.length ≤ N := by
  simp only [wordBall, mem_biUnion, mem_range, mem_words]
  constructor
  · rintro ⟨n, hn, rfl⟩; omega
  · intro h; exact ⟨w.length, by omega, rfl⟩

omit [Fintype α] in
lemma reduced_boundary_product (u v h : Word α) (hr : IsReduced (u ++ h)) :
    reduce ((u ++ v) ++ (invRev v ++ h)) = u ++ h := by
  have heq : FreeGroup.mk ((u ++ v) ++ (invRev v ++ h)) = FreeGroup.mk (u ++ h) := by
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    group
  have ht := congr_arg FreeGroup.toWord heq
  simpa only [FreeGroup.toWord_mk, hr.reduce_eq] using ht

omit [Fintype α] in
 
lemma boundary_unique {u v h u' v' h' : Word α}
    (hr : IsReduced (u ++ h)) (hr' : IsReduced (u' ++ h'))
    (hw : u ++ v = u' ++ v') (hx : invRev v ++ h = invRev v' ++ h') :
    u = u' ∧ v = v' ∧ h = h' := by
  have hout : u ++ h = u' ++ h' := by
    rw [← reduced_boundary_product u v h hr, hw, hx,
      reduced_boundary_product u' v' h' hr']
  have hwL := congrArg List.length hw
  have hxL := congrArg List.length hx
  have hyL := congrArg List.length hout
  simp only [List.length_append, invRev_length] at hwL hxL hyL
  have hvL : v.length = v'.length := by omega
  have hu : u = u' := List.append_inj_left' hw hvL
  subst u'
  have hv : v = v' := List.append_cancel_left hw
  subst v'
  exact ⟨rfl, rfl, List.append_cancel_left hx⟩

omit [Fintype α] [DecidableEq α] in
lemma append_injOn {su sv : Finset (Word α)} {l : ℕ}
    (hU : ∀ u ∈ su, u.length = l) :
    Set.InjOn (fun p : Word α × Word α => p.1 ++ p.2) (↑(su ×ˢ sv) : Set _) := by
  rintro ⟨u,v⟩ hp ⟨u',v'⟩ hp' h
  have hp₁ : u ∈ su ∧ v ∈ sv := by simpa only [mem_coe, mem_product] using hp
  have hp₂ : u' ∈ su ∧ v' ∈ sv := by simpa only [mem_coe, mem_product] using hp'
  have hu : u = u' := List.append_inj_left h
    ((hU u hp₁.1).trans (hU u' hp₂.1).symm)
  subst u'
  exact Prod.ext rfl (List.append_cancel_left h)

omit [Fintype α] [DecidableEq α] in
lemma invRev_append_injOn {sv sh : Finset (Word α)} {l : ℕ}
    (hV : ∀ v ∈ sv, v.length = l) :
    Set.InjOn (fun p : Word α × Word α => invRev p.1 ++ p.2) (↑(sv ×ˢ sh) : Set _) := by
  rintro ⟨v,h⟩ hp ⟨v',h'⟩ hp' hh
  have hp₁ : v ∈ sv ∧ h ∈ sh := by simpa only [mem_coe, mem_product] using hp
  have hp₂ : v' ∈ sv ∧ h' ∈ sh := by simpa only [mem_coe, mem_product] using hp'
  have hv : invRev v = invRev v' := List.append_inj_left hh (by
    simp only [invRev_length]
    exact (hV v hp₁.1).trans (hV v' hp₂.1).symm)
  have hv' : v = v' := by simpa using congrArg invRev hv
  subst v'
  exact Prod.ext rfl (List.append_cancel_left hh)

omit [Fintype α] [DecidableEq α] in
lemma sum_sq_comp_le {I J : Type*} [DecidableEq J]
    (si : Finset I) (sj : Finset J) (out : I → J) (c : J → ℂ)
    (hinj : Set.InjOn out si) (hzero : ∀ i ∈ si, out i ∉ sj → c (out i) = 0) :
    ∑ i ∈ si, ‖c (out i)‖ ^ 2 ≤ ∑ j ∈ sj, ‖c j‖ ^ 2 := by
  classical
  let ss := si.filter (fun i => out i ∈ sj)
  have heq : ∑ i ∈ si, ‖c (out i)‖ ^ 2 = ∑ i ∈ ss, ‖c (out i)‖ ^ 2 := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hnot
    have hz : c (out i) = 0 := hzero i hi (by
      intro hh; exact hnot (mem_filter.mpr ⟨hi,hh⟩))
    simp [hz]
  rw [heq, ← sum_image (f := fun j => ‖c j‖ ^ 2) (s := ss)
    (hinj.mono (by exact filter_subset _ _))]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact (mem_filter.mp hi).2
  · intros; positivity

lemma coefficient_energy_le (q t : ℕ) (ht : t ≤ q) (c : Word α → ℂ) :
    ∑ u ∈ words (q-t), ∑ v ∈ words t, ‖c (u ++ v)‖ ^ 2 ≤
      ∑ w ∈ words q, ‖c w‖ ^ 2 := by
  have hb := sum_sq_comp_le (words (α := α) (q-t) ×ˢ words t) (words q)
    (fun p : Word α × Word α => p.1 ++ p.2) c (append_injOn (l := q-t) (by simp)) (by
      intro p hp hn
      have hh : p.1.length = q-t ∧ p.2.length = t := by simpa using hp
      exact (hn (by simp [hh, Nat.sub_add_cancel ht])).elim)
  simpa only [sum_product] using hb

lemma input_energy_le (N t : ℕ) (f : Word α → ℂ)
    (hf : ∀ w, N < w.length → f w = 0) :
    ∑ h ∈ wordBall N, ∑ v ∈ words t, ‖f (invRev v ++ h)‖ ^ 2 ≤
      ∑ x ∈ wordBall N, ‖f x‖ ^ 2 := by
  have hb := sum_sq_comp_le (words (α := α) t ×ˢ wordBall N) (wordBall N)
    (fun p : Word α × Word α => invRev p.1 ++ p.2) f
    (invRev_append_injOn (l := t) (by simp)) (by
      intro p _ hp
      exact hf _ (by simpa using hp))
  rw [sum_comm]
  simpa only [sum_product] using hb

def piece (q N t : ℕ) (c f : Word α → ℂ) : Vector (Word α) := by
  classical
  exact ∑ p ∈ ((wordBall N) ×ˢ words (q-t)).filter (fun p => IsReduced (p.2 ++ p.1)),
    lp.single 2 (p.2 ++ p.1) (∑ v ∈ words t, c (p.2 ++ v) * f (invRev v ++ p.1))

lemma piece_norm_sq_le (q N t : ℕ) (ht : t ≤ q) (c f : Word α → ℂ)
    (hf : ∀ w, N < w.length → f w = 0) :
    ‖piece q N t c f‖ ^ 2 ≤
      (∑ w ∈ words q, ‖c w‖ ^ 2) * ∑ x ∈ wordBall N, ‖f x‖ ^ 2 := by
  classical
  have hi : Set.InjOn (fun p : Word α × Word α => p.2 ++ p.1)
      {p | p.1 ∈ wordBall N ∧ p.2 ∈ words (q-t) ∧ IsReduced (p.2 ++ p.1)} := by
    rintro ⟨h,u⟩ hp ⟨h',u'⟩ hp' heq
    have hu : u = u' := List.append_inj_left heq
      ((mem_words.mp hp.2.1).trans (mem_words.mp hp'.2.1).symm)
    subst u'
    exact Prod.ext (List.append_cancel_left heq) rfl
  have hb := masked_block_matrix_bound (words (q-t)) (words t) (wordBall N)
    (fun u v => c (u ++ v)) (fun v h => f (invRev v ++ h))
    (fun u h => IsReduced (u ++ h)) (fun u h => u ++ h) hi
  exact hb.trans (mul_le_mul (coefficient_energy_le q t ht c)
    (input_energy_le N t f hf) (by positivity) (by positivity))

lemma piece_norm_le (q N t : ℕ) (ht : t ≤ q) (c f : Word α → ℂ)
    (hf : ∀ w, N < w.length → f w = 0) :
    ‖piece q N t c f‖ ≤
      Real.sqrt (∑ w ∈ words q, ‖c w‖ ^ 2) *
        Real.sqrt (∑ x ∈ wordBall N, ‖f x‖ ^ 2) := by
  have hc0 : 0 ≤ ∑ w ∈ words (α := α) q, ‖c w‖ ^ 2 := by positivity
  have hf0 : 0 ≤ ∑ x ∈ wordBall (α := α) N, ‖f x‖ ^ 2 := by positivity
  have hsq : (Real.sqrt (∑ w ∈ words (α := α) q, ‖c w‖ ^ 2) *
      Real.sqrt (∑ x ∈ wordBall (α := α) N, ‖f x‖ ^ 2)) ^ 2 =
      (∑ w ∈ words q, ‖c w‖ ^ 2) * ∑ x ∈ wordBall N, ‖f x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc0, Real.sq_sqrt hf0]
  have hb := piece_norm_sq_le q N t ht c f hf
  rw [← hsq] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

omit [Fintype α] [DecidableEq α] in
lemma single_sum {I J : Type*} [DecidableEq J] (s : Finset I) (j : J) (c : I → ℂ) :
    (lp.single 2 j (∑ i ∈ s, c i) : Vector J) = ∑ i ∈ s, lp.single 2 j (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [sum_insert ha, lp.single_add, ih]

def tripleBox (q N t : ℕ) : Finset ((Word α × Word α) × Word α) := by
  classical
  exact (((wordBall N) ×ˢ words (q-t)).filter
    (fun p => IsReduced (p.2 ++ p.1))) ×ˢ words t

def triples (q N : ℕ) : Finset (Σ _ : ℕ, (Word α × Word α) × Word α) :=
  (range (q+1)).sigma (tripleBox q N)

@[simp] lemma mem_triples (q N t : ℕ) (h u v : Word α) :
    Sigma.mk t ((h,u),v) ∈ triples q N ↔
      t ≤ q ∧ h.length ≤ N ∧ u.length = q-t ∧ IsReduced (u ++ h) ∧ v.length = t := by
  classical
  simp [triples, tripleBox, and_assoc]

def tripleValue (c f : Word α → ℂ) (p : Σ _ : ℕ, (Word α × Word α) × Word α) :
    Vector (Word α) :=
  lp.single 2 (p.2.1.2 ++ p.2.1.1) (c (p.2.1.2 ++ p.2.2) * f (invRev p.2.2 ++ p.2.1.1))

def triplePair (p : Σ _ : ℕ, (Word α × Word α) × Word α) : Word α × Word α :=
  (p.2.1.2 ++ p.2.2, invRev p.2.2 ++ p.2.1.1)

def convolution (q N : ℕ) (c f : Word α → ℂ) : Vector (Word α) :=
  ∑ p ∈ words q ×ˢ wordBall N,
    lp.single 2 (reduce (p.1 ++ p.2)) (c p.1 * f p.2)

lemma sum_pieces (q N : ℕ) (c f : Word α → ℂ) :
    ∑ t ∈ range (q+1), piece q N t c f =
      ∑ p ∈ triples q N, tripleValue c f p := by
  classical
  unfold triples
  rw [← sum_sigma' (range (q+1)) (tripleBox q N)
    (fun t p => tripleValue c f ⟨t,p⟩)]
  apply sum_congr rfl
  intro t _
  unfold piece tripleBox
  rw [sum_product]
  apply sum_congr rfl
  intro p _
  exact single_sum (words t) (p.2 ++ p.1) _

lemma convolution_eq_pieces (q N : ℕ) (c f : Word α → ℂ)
    (hc : ∀ w, c w ≠ 0 → IsReduced w)
    (hfr : ∀ w, f w ≠ 0 → IsReduced w)
    (hfN : ∀ w, N < w.length → f w = 0) :
    convolution q N c f = ∑ t ∈ range (q+1), piece q N t c f := by
  classical
  rw [sum_pieces]
  unfold convolution
  symm
  apply sum_bij_ne_zero (fun p _ _ => triplePair p)
  · rintro ⟨t,⟨⟨h,u⟩,v⟩⟩ hp hn
    obtain ⟨ht, hh, hu, hr, hv⟩ := (mem_triples q N t h u v).mp hp
    simp only [triplePair, mem_product, mem_words, mem_wordBall, List.length_append,
      invRev_length]
    refine ⟨by omega, ?_⟩
    by_contra! hgt
    have hz := hfN (invRev v ++ h) (by simpa using hgt)
    exact hn (by simp [tripleValue, hz])
  · rintro ⟨t,⟨⟨h,u⟩,v⟩⟩ hp _ ⟨t',⟨⟨h',u'⟩,v'⟩⟩ hp' _ heq
    obtain ⟨ht, hh, hu, hr, hv⟩ := (mem_triples q N t h u v).mp hp
    obtain ⟨ht', hh', hu', hr', hv'⟩ := (mem_triples q N t' h' u' v').mp hp'
    have hw : u ++ v = u' ++ v' := congrArg Prod.fst heq
    have hx : invRev v ++ h = invRev v' ++ h' := congrArg Prod.snd heq
    obtain ⟨rfl,rfl,rfl⟩ := boundary_unique hr hr' hw hx
    have htt : t = t' := hv.symm.trans hv'
    cases htt
    rfl
  · rintro ⟨w,x⟩ hp hn
    have hwL : w.length = q := mem_words.mp (mem_product.mp hp).1
    have hxL : x.length ≤ N := mem_wordBall.mp (mem_product.mp hp).2
    have hcw : c w ≠ 0 := by
      intro hz
      exact hn (by simp [hz])
    have hfx : f x ≠ 0 := by
      intro hz
      exact hn (by simp [hz])
    obtain ⟨u,v,h,hw,hx,hy,hr⟩ :=
      HochschildFreeWords.boundary_reduction w x (hc w hcw) (hfr x hfx)
    have hwLen : u.length + v.length = q := by simpa [hw] using hwL
    have hxLen : v.length + h.length ≤ N := by simpa [hx] using hxL
    let p : Σ _ : ℕ, (Word α × Word α) × Word α := ⟨v.length,((h,u),v)⟩
    have hpm : p ∈ triples q N := (mem_triples q N _ _ _ _).mpr
      ⟨by omega, by omega, by omega, hr, rfl⟩
    have hpvalue : tripleValue c f p =
        lp.single 2 (reduce (w ++ x)) (c w * f x) := by
      simp only [tripleValue, p, ← hw, ← hx, hy]
    refine ⟨p,hpm,?_,?_⟩
    · rwa [hpvalue]
    · exact Prod.ext hw.symm hx.symm
  · rintro ⟨t,⟨⟨h,u⟩,v⟩⟩ hp _
    obtain ⟨ht, hh, hu, hr, hv⟩ := (mem_triples q N t h u v).mp hp
    simp only [tripleValue, triplePair, reduced_boundary_product u v h hr]

 

theorem convolution_norm_le (q N : ℕ) (c f : Word α → ℂ)
    (hc : ∀ w, c w ≠ 0 → IsReduced w)
    (hfr : ∀ w, f w ≠ 0 → IsReduced w)
    (hfN : ∀ w, N < w.length → f w = 0) :
    ‖convolution q N c f‖ ≤ (q+1 : ℝ) *
      Real.sqrt (∑ w ∈ words q, ‖c w‖ ^ 2) *
        Real.sqrt (∑ x ∈ wordBall N, ‖f x‖ ^ 2) := by
  rw [convolution_eq_pieces q N c f hc hfr hfN]
  calc
    _ ≤ ∑ t ∈ range (q+1), ‖piece q N t c f‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ range (q+1), Real.sqrt (∑ w ∈ words q, ‖c w‖ ^ 2) *
        Real.sqrt (∑ x ∈ wordBall N, ‖f x‖ ^ 2) := by
      apply sum_le_sum
      intro t ht
      exact piece_norm_le q N t (by simpa using ht) c f hfN
    _ = _ := by simp [mul_assoc]

end
end HochschildLength

namespace HochschildTransfer
open Finset FreeGroup
open HochschildLength
noncomputable section
variable {α : Type*} [DecidableEq α]
abbrev Polynomial (α : Type*) := MonoidAlgebra ℂ (FreeGroup α)

def vector : Polynomial α →ₗ[ℂ] Vector (Word α) :=
  (Finsupp.lsum ℂ (fun g : FreeGroup α => lp.lsingle (𝕜 := ℂ) (E := fun _ : Word α => ℂ) 2 g.toWord)).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

lemma vector_def (p : Polynomial α) : vector p =
    ∑ g ∈ p.coeff.support, lp.single 2 g.toWord (p.coeff g) := by
  rfl

@[simp] lemma vector_single (g : FreeGroup α) (c : ℂ) :
    vector (MonoidAlgebra.single g c) = lp.single 2 g.toWord c := by
  simp [vector]

lemma vector_norm_sq (p : Polynomial α) :
    ‖vector p‖^2 = ∑ g ∈ p.coeff.support, ‖p.coeff g‖^2 := by
  rw [vector_def]
  exact norm_sum_single_sq _ _ _ (toWord_injective.injOn)

def wordCoeff (p : Polynomial α) (w : Word α) : ℂ := by
  classical
  exact if IsReduced w then p.coeff (mk w) else 0

@[simp] lemma wordCoeff_toWord (p : Polynomial α) (g : FreeGroup α) :
    wordCoeff p g.toWord = p.coeff g := by
  simp [wordCoeff, isReduced_toWord, mk_toWord]

omit [DecidableEq α] in
lemma reduced_of_wordCoeff_ne_zero (p : Polynomial α) (w : Word α)
    (h : wordCoeff p w ≠ 0) : IsReduced w := by
  classical
  by_contra hn
  simp [wordCoeff, hn] at h

omit [DecidableEq α] in
lemma wordCoeff_eq_zero (p : Polynomial α) (w : Word α)
    (h : p.coeff (mk w) = 0) : wordCoeff p w = 0 := by
  simp [wordCoeff, h]

lemma sum_wordCoeff (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s)
    {V : Type*} [AddCommMonoid V] (F : Word α → ℂ → V)
    (hzero : ∀ w, F w 0 = 0) :
    (∑ w ∈ s, F w (wordCoeff p w)) =
      ∑ g ∈ p.coeff.support, F g.toWord (p.coeff g) := by
  classical
  calc
    _ = ∑ w ∈ p.coeff.support.image toWord, F w (wordCoeff p w) := by
      symm
      apply sum_subset
      · intro w hw
        obtain ⟨g,hg,rfl⟩ := mem_image.mp hw
        exact hs g hg
      · intro w hw hnot
        by_cases hr : IsReduced w
        · have hm : mk w ∉ p.coeff.support := by
            intro hm
            apply hnot
            exact mem_image.mpr ⟨mk w, hm, by simpa [toWord_mk] using hr.reduce_eq⟩
          simp [wordCoeff, hr, Finsupp.notMem_support_iff.mp hm, hzero]
        · simp [wordCoeff, hr, hzero]
    _ = _ := by
      rw [sum_image toWord_injective.injOn]
      simp only [wordCoeff_toWord]

lemma polynomial_wordSum (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s) :
    (∑ w ∈ s, MonoidAlgebra.single (mk w) (wordCoeff p w)) = p := by
  rw [sum_wordCoeff p s hs _ (by simp)]
  simpa only [mk_toWord, Finsupp.sum] using p.sum_coeff_single

lemma vector_wordSum (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s) :
    (∑ w ∈ s, lp.single 2 w (wordCoeff p w)) = vector p := by
  rw [sum_wordCoeff p s hs _ (by simp), vector_def]

lemma vector_mul_wordSum (p d : Polynomial α) (S T : Finset (Word α))
    (hS : ∀ g ∈ p.coeff.support, g.toWord ∈ S)
    (hT : ∀ g ∈ d.coeff.support, g.toWord ∈ T) :
    vector (p*d) = ∑ v ∈ S, ∑ w ∈ T,
      lp.single 2 (reduce (v++w)) (wordCoeff p v * wordCoeff d w) := by
  conv_lhs => rw [← polynomial_wordSum p S hS, ← polynomial_wordSum d T hT]
  simp only [sum_mul, mul_sum, map_sum, MonoidAlgebra.single_mul_single, vector_single,
    FreeGroup.mul_mk, toWord_mk]
  rw [sum_comm]

lemma vector_norm_sq_wordSum (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s) :
    ‖vector p‖^2 = ∑ w ∈ s, ‖wordCoeff p w‖^2 := by
  rw [← vector_wordSum p s hs]
  exact norm_sum_single_sq s id _ (Function.injective_id.injOn)

variable [Fintype α]
lemma vector_mul_norm_le (p d : Polynomial α) (q : ℕ)
    (hq : ∀ g ∈ p.coeff.support, g.toWord.length = q) :
    ‖vector (p*d)‖ ≤ (q+1:ℝ) * ‖vector p‖ * ‖vector d‖ := by
  let N := d.coeff.support.sup (fun g => g.toWord.length)
  have hq' : ∀ g ∈ p.coeff.support, g.toWord ∈ words q := by
    simpa only [mem_words] using hq
  have hN : ∀ g ∈ d.coeff.support, g.toWord ∈ wordBall N := by
    intro g hg
    rw [mem_wordBall]
    exact le_sup (f := fun g : FreeGroup α => g.toWord.length) hg
  have heq : vector (p*d) = convolution q N (wordCoeff p) (wordCoeff d) := by
    rw [vector_mul_wordSum p d _ _ hq' hN]
    unfold HochschildLength.convolution
    exact (sum_product (words q) (wordBall N)
      (fun z : Word α × Word α => (lp.single 2 (reduce (z.1++z.2))
        (wordCoeff p z.1 * wordCoeff d z.2) : Vector (Word α)))).symm
  rw [heq]
  have h := convolution_norm_le q N (wordCoeff p) (wordCoeff d)
    (reduced_of_wordCoeff_ne_zero p) (reduced_of_wordCoeff_ne_zero d) (by
      intro w hw
      classical
      by_cases hr : IsReduced w
      · apply wordCoeff_eq_zero
        by_contra hn
        have hmem := hN (mk w) (Finsupp.mem_support_iff.mpr hn)
        rw [mem_wordBall, toWord_mk, hr.reduce_eq] at hmem
        omega
      · simp [wordCoeff, hr])
  rw [← vector_norm_sq_wordSum p _ hq', ← vector_norm_sq_wordSum d _ hN,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact h

end
end HochschildTransfer

namespace HochschildTracePolynomial
open Finset
open scoped ComplexOrder
noncomputable section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {G : Type*} [Group G] [DecidableEq G]
variable (τ : A →ₚ[ℂ] ℂ) (u : G →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : G, g ≠ 1 → τ (u g) = 0)

include hτ hu hfree

lemma inner_word (g h : G) :
    inner ℂ (τ.toPreGNS (u g)) (τ.toPreGNS (u h)) = if g = h then 1 else 0 := by
  classical
  rw [PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, hu, ← map_mul]
  split_ifs with heq
  · subst h
    simp [hτ]
  · apply hfree
    exact fun h => heq (_root_.inv_mul_eq_one.mp h)

lemma norm_sum_word_sq (s : Finset G) (c : G → ℂ) :
    ‖τ.toPreGNS (∑ g ∈ s, c g • u g)‖^2 = ∑ g ∈ s, ‖c g‖^2 := by
  classical
  have hi : inner ℂ (τ.toPreGNS (∑ g ∈ s, c g • u g))
      (τ.toPreGNS (∑ g ∈ s, c g • u g)) = ∑ g ∈ s, (‖c g‖ : ℂ)^2 := by
    simp only [map_sum, map_smul]
    rw [sum_inner]
    apply sum_congr rfl
    intro g hg
    rw [inner_sum, sum_eq_single g]
    · rw [inner_smul_left, inner_smul_right, inner_word τ u hτ hu hfree]
      simp [Complex.conj_mul']
    · intro h hh hne
      rw [inner_smul_left, inner_smul_right, inner_word τ u hτ hu hfree]
      simp [Ne.symm hne]
    · exact fun h => (h hg).elim
  apply Complex.ofReal_injective
  simpa [inner_self_eq_norm_sq_to_K, Complex.ofReal_sum, Complex.ofReal_pow] using hi

lemma norm_eval_sq (p : MonoidAlgebra ℂ G) :
    ‖τ.toPreGNS (MonoidAlgebra.lift ℂ A G u p)‖^2 =
      ∑ g ∈ p.coeff.support, ‖p.coeff g‖^2 := by
  rw [MonoidAlgebra.lift_apply]
  exact norm_sum_word_sq τ u hτ hu hfree _ _

end
end HochschildTracePolynomial

namespace HochschildPolynomial
open Finset
noncomputable section
variable {G : Type*} [Group G]

def adjoint (p : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  .ofCoeff ((p.coeff.mapRange (starRingEnd ℂ) (map_zero _)).mapDomain Inv.inv)

@[simp] lemma coeff_adjoint (p : MonoidAlgebra ℂ G) (g : G) :
    (adjoint p).coeff g = star (p.coeff g⁻¹) := by
  have h := Finsupp.mapDomain_apply_of_injective inv_injective
    (p.coeff.mapRange (starRingEnd ℂ) (map_zero _)) g⁻¹
  simpa [adjoint] using h

lemma adjoint_support (p : MonoidAlgebra ℂ G) (g : G) :
    g ∈ (adjoint p).coeff.support ↔ g⁻¹ ∈ p.coeff.support := by
  simp [Finsupp.mem_support_iff]

variable {A : Type*} [CStarAlgebra A]
lemma eval_adjoint (u : G →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (p : MonoidAlgebra ℂ G) :
    MonoidAlgebra.lift ℂ A G u (adjoint p) = star (MonoidAlgebra.lift ℂ A G u p) := by
  classical
  simp only [MonoidAlgebra.lift_apply, adjoint]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, star_sum, star_smul, hu, Complex.star_def]

end
end HochschildPolynomial

open scoped ComplexOrder
open Filter Topology
namespace HochschildTransfer
open Finset
open scoped ComplexOrder
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)
include hτ hu hfree
omit [Fintype α] in
lemma vector_norm_eq_preGNS (p : Polynomial α) :
    ‖vector p‖ = ‖τ.toPreGNS (MonoidAlgebra.lift ℂ A (FreeGroup α) u p)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [vector_norm_sq, HochschildTracePolynomial.norm_eval_sq τ u hτ hu hfree]

omit hτ hu hfree in
lemma norm_one_gns (h1 : τ 1 = 1) : ‖τ.toPreGNS 1‖ = 1 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS 1))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at h
  nlinarith [norm_nonneg (τ.toPreGNS 1)]

omit hτ hu hfree in
lemma norm_star_gns (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _

 

theorem norm_eval_homogeneous_le
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (p : Polynomial α) (q : ℕ)
    (hq : ∀ g ∈ p.coeff.support, g.toWord.length = q) :
    ‖MonoidAlgebra.lift ℂ A (FreeGroup α) u p‖ ≤
      (q+1:ℝ) * ‖τ.toPreGNS (MonoidAlgebra.lift ℂ A (FreeGroup α) u p)‖ := by
  let E := MonoidAlgebra.lift ℂ A (FreeGroup α) u
  let C : ℝ := (q+1:ℝ) * ‖τ.toPreGNS (E p)‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (d : Polynomial α) :
      ‖τ.toPreGNS (E (p*d))‖ ≤ C * ‖τ.toPreGNS (E d)‖ := by
    simpa only [vector_norm_eq_preGNS τ u hτ hu hfree] using
      vector_mul_norm_le p d q hq
  have hqa : ∀ g ∈ (HochschildPolynomial.adjoint p).coeff.support,
      g.toWord.length = q := by
    intro g hg
    have h := hq g⁻¹ ((HochschildPolynomial.adjoint_support p g).mp hg)
    simpa only [FreeGroup.toWord_inv, FreeGroup.invRev_length] using h
  have hpa (d : Polynomial α) :
      ‖τ.toPreGNS (E (HochschildPolynomial.adjoint p*d))‖ ≤
        C * ‖τ.toPreGNS (E d)‖ := by
    have h := vector_mul_norm_le (HochschildPolynomial.adjoint p) d q hqa
    simp only [vector_norm_eq_preGNS τ u hτ hu hfree,
      HochschildPolynomial.eval_adjoint u hu, norm_star_gns τ htr] at h
    exact h
  let a : Polynomial α := HochschildPolynomial.adjoint p * p
  have ha : E a = star (E p) * E p := by
    simp only [a, map_mul, E, HochschildPolynomial.eval_adjoint u hu]
  have hpow (n : ℕ) : ‖τ.toPreGNS (E (a^n))‖ ≤ (C^2)^n := by
    induction n with
    | zero => simp [norm_one_gns τ hτ]
    | succ n ih =>
      calc
        _ = ‖τ.toPreGNS (E (HochschildPolynomial.adjoint p*(p*a^n)))‖ := by
          rw [pow_succ']; simp only [a, mul_assoc]
        _ ≤ C * ‖τ.toPreGNS (E (p*a^n))‖ := hpa _
        _ ≤ C * (C * ‖τ.toPreGNS (E (a^n))‖) := mul_le_mul_of_nonneg_left (hp _) hC
        _ ≤ C * (C * (C^2)^n) := by gcongr
        _ = _ := by ring
  have hmoment (n : ℕ) : (τ ((star (E p)*E p)^n)).re ≤ (C^2)^n := by
    have hinner : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS (E (a^n))) =
        τ ((star (E p)*E p)^n) := by
      simp only [PositiveLinearMap.preGNS_inner_def,
        PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, map_pow, ha]
    calc
      _ ≤ ‖τ ((star (E p)*E p)^n)‖ := Complex.re_le_norm _
      _ = ‖inner ℂ (τ.toPreGNS 1) (τ.toPreGNS (E (a^n)))‖ := congrArg norm hinner.symm
      _ ≤ ‖τ.toPreGNS 1‖ * ‖τ.toPreGNS (E (a^n))‖ := norm_inner_le_norm _ _
      _ ≤ (C^2)^n := by rw [norm_one_gns τ hτ, one_mul]; exact hpow n
  have hn := HochschildMoments.norm_le_of_positive_moment_bound τ hfaith
    (star (E p)*E p) (star_mul_self_nonneg _) (C^2) (sq_nonneg _) hmoment
  rw [CStarRing.norm_star_mul_self] at hn
  change ‖E p‖ ≤ C
  nlinarith [norm_nonneg (E p)]

end
end HochschildTransfer
end

end OAI
