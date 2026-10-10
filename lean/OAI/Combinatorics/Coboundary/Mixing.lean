import OAI.Combinatorics.Coboundary.LinkSpectrum
import OAI.Combinatorics.Coboundary.FatLadders
import OAI.Combinatorics.Coboundary.Spectral
import OAI.GroupTheory.Congruence.Elementary

namespace OAI

noncomputable section

/-!
Small-set expansion, local spectral descent, connectedness, and uniform coset mixing.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

def volume (e : V → V → ℝ) : ℝ := ∑ x, mass e x
def selected (e : V → V → ℝ) (P : V → Prop) : ℝ := ∑ x, if P x then mass e x else 0
def chi (P : V → Prop) (x : V) : ℝ := if P x then 1 else 0

lemma mean_chi (e : V → V → ℝ) (P : V → Prop) :
    (∑ x, mass e x * chi P x) = selected e P := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P x <;> simp [chi,h]

omit [Fintype V] in
lemma chi_sq (P : V → Prop) (x : V) : (chi P x)^2 = chi P x := by
  by_cases h : P x <;> simp [chi,h]

lemma sum_right (e : V → V → ℝ) (hs : ∀ x y, e x y = e y x) (f : V → ℝ) :
    (∑ x, ∑ y, e x y * f y) = ∑ x, mass e x * f x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [hs]

lemma centered_mean (e : V → V → ℝ) (P : V → Prop) :
    (∑ x, mass e x * (volume e * chi P x - selected e P)) = 0 := by
  simp only [mul_sub,Finset.sum_sub_distrib]
  have h : (∑ x, mass e x * (volume e * chi P x)) = volume e * selected e P := by
    rw [← mean_chi,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h,← Finset.sum_mul]
  change volume e * selected e P - volume e * selected e P = 0
  ring

lemma centered_energy (e : V → V → ℝ) (P : V → Prop) :
    energy e (fun x => volume e * chi P x - selected e P) =
      (volume e)^2*selected e P-volume e*(selected e P)^2 := by
  have he : energy e (fun x => volume e * chi P x - selected e P) =
      (volume e)^2*(∑ x, mass e x * chi P x) -
      2*volume e*selected e P*(∑ x, mass e x * chi P x) +
      (selected e P)^2*(∑ x, mass e x) := by
    simp only [energy,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P x <;> simp [chi, h] <;> ring
  rw [he,mean_chi]
  change (volume e)^2*selected e P - 2*volume e*selected e P*selected e P +
    (selected e P)^2*volume e = _
  ring

lemma centered_pairing (e : V → V → ℝ) (hs : ∀ x y, e x y = e y x) (P : V → Prop) :
    pairing e (fun x => volume e * chi P x - selected e P)
      (fun x => volume e * chi P x - selected e P) =
    (volume e)^2*pairing e (chi P) (chi P)-volume e*(selected e P)^2 := by
  have he : pairing e (fun x => volume e * chi P x - selected e P)
      (fun x => volume e * chi P x - selected e P) =
      (volume e)^2*pairing e (chi P) (chi P) -
      volume e*selected e P*(∑ x, ∑ y, e x y * chi P x) -
      volume e*selected e P*(∑ x, ∑ y, e x y * chi P y) +
      (selected e P)^2*volume e := by
    simp only [pairing,volume,mass,Finset.mul_sum,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hl : (∑ x, ∑ y, e x y * chi P x) = selected e P := by
    simp only [← Finset.sum_mul]
    exact mean_chi e P
  rw [he,hl,sum_right e hs,mean_chi]
  ring

theorem small_set (e : V → V → ℝ) (he : ∀ x y, 0 ≤ e x y)
    (hs : ∀ x y, e x y = e y x) (hvol : 0 < volume e)
    {lam t : ℝ} (hlam : 0 ≤ lam) (hray : Rayleigh e lam)
    (P : V → Prop) (hP : selected e P ≤ t*volume e) :
    pairing e (chi P) (chi P) ≤ (t+lam)*selected e P := by
  have ha : 0 ≤ selected e P := Finset.sum_nonneg (fun x _ => by
    split_ifs
    · exact Finset.sum_nonneg (fun y _ => he x y)
    · rfl)
  have hh := hray (fun x => volume e * chi P x - selected e P) (centered_mean e P)
  rw [centered_pairing e hs,centered_energy] at hh
  have hb : volume e*(selected e P)^2 ≤ t*(volume e)^2*selected e P := by
    nlinarith [mul_le_mul_of_nonneg_right hP (mul_nonneg hvol.le ha)]
  have hn : 0 ≤ lam*volume e*(selected e P)^2 := by positivity
  have hv : 0 < (volume e)^2 := sq_pos_of_pos hvol
  nlinarith

end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
lemma coface_eq_insert {s a : Finset V} (hsub : s ⊆ a) (hc : a.card = s.card+1) :
    ∃ x, x ∉ s ∧ insert x s = a := by
  obtain ⟨x,hxa,hxs⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : s.card < a.card)
  refine ⟨x,hxs,Finset.eq_of_subset_of_card_le (Finset.insert_subset hxa hsub) ?_⟩
  rw [Finset.card_insert_of_notMem hxs,hc]

lemma sum_insert_star (s : Finset V) (g : Finset V → ℝ) :
    (∑ x : V, if x ∉ s then g (insert x s) else 0) = starSum (s.card+1) s g := by
  unfold starSum
  rw [← Finset.sum_filter,← Finset.sum_filter]
  apply Finset.sum_bij (fun x _ => insert x s)
  · intro x hx
    have hn := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨mem_level.mpr (Finset.card_insert_of_notMem hn),
      Finset.subset_insert _ _⟩
  · intro x hx y hy he
    have hxs := (Finset.mem_filter.mp hx).2
    have hys := (Finset.mem_filter.mp hy).2
    have hm : x ∈ insert y s := he ▸ Finset.mem_insert_self x s
    exact (Finset.mem_insert.mp hm).resolve_right hxs
  · intro a ha
    obtain ⟨ha,hsub⟩ := Finset.mem_filter.mp ha
    obtain ⟨x,hx,he⟩ := coface_eq_insert hsub (mem_level.mp ha)
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,he⟩
  · intro x hx
    rfl

def linkEdge (w : Finset V → ℝ) (s : Finset V) (x y : V) : ℝ :=
  if x ∉ s ∧ y ∉ s ∧ x ≠ y then w (insert x (insert y s)) else 0

omit [Fintype V] in
lemma linkEdge_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (s x y) :
    0 ≤ linkEdge w s x y := by unfold linkEdge; split_ifs; exact hw _; rfl
omit [Fintype V] in
lemma linkEdge_symm (w : Finset V → ℝ) (s : Finset V) (x y : V) :
    linkEdge w s x y = linkEdge w s y x := by
  simp only [linkEdge,Finset.insert_comm,ne_comm,and_comm,and_left_comm,and_assoc]

lemma linkEdge_mass {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (x : V) :
    EdgeMixing.mass (linkEdge w s) x =
      if x ∉ s then (N-s.card-1:ℕ)*w (insert x s) else 0 := by
  by_cases hx : x ∈ s
  · simp [EdgeMixing.mass,linkEdge,hx]
  · rw [ite_eq_left hx]
    have he : EdgeMixing.mass (linkEdge w s) x =
        ∑ y : V, if y ∉ insert x s then w (insert y (insert x s)) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ s
      · simp [linkEdge,hy]
      · by_cases hxy : x = y
        · subst y; simp [linkEdge]
        · simp [linkEdge,hx,hy,hxy,Ne.symm hxy,Finset.insert_comm]
    rw [he,sum_insert_star,hw.balance _ _ (by omega)]
    simp [Finset.card_insert_of_notMem hx,Nat.sub_add_eq]

lemma linkEdge_selected {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (F : Finset V → Prop) (s : Finset V) :
    EdgeMixing.selected (linkEdge w s) (fun x => F (insert x s)) =
      (N-s.card-1:ℕ)*starNorm w (s.card+1) s (indicator F) := by
  have he : EdgeMixing.selected (linkEdge w s) (fun x => F (insert x s)) =
      (N-s.card-1:ℕ)*(∑ x : V, if x ∉ s then atom w (indicator F) (insert x s) else 0) := by
    simp only [EdgeMixing.selected,linkEdge_mass hw,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [atom_indicator]
    split_ifs <;> ring
  rw [he,sum_insert_star]
  rfl

lemma linkEdge_volume {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) :
    EdgeMixing.volume (linkEdge w s) =
      (N-s.card-1:ℕ)*(N-s.card:ℕ)*w s := by
  have he : EdgeMixing.volume (linkEdge w s) =
      (N-s.card-1:ℕ)*(∑ x : V, if x ∉ s then w (insert x s) else 0) := by
    simp only [EdgeMixing.volume,linkEdge_mass hw,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he,sum_insert_star,hw.balance _ _ (by omega)]
  simp [mul_assoc]

omit [Fintype V] in
lemma Collision.reconstruct {F : Finset V → Prop} {s a : Finset V}
    (hc : Collision F s a) : ∃ x y, x ∉ s ∧ y ∉ s ∧ x ≠ y ∧
      a = insert x (insert y s) ∧ F (insert x s) ∧ F (insert y s) := by
  obtain ⟨x,hx,y,hy,hxy,he,hfx,hfy⟩ := hc
  have hye : y ∈ a.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
  have hey : insert y s = a.erase x := by rw [←he,Finset.insert_erase hye]
  have hrep : insert x (insert y s) = a := by rw [hey,Finset.insert_erase hx]
  have hex : insert x s = a.erase y := by
    rw [←he,Finset.erase_right_comm,Finset.insert_erase]
    exact Finset.mem_erase.mpr ⟨hxy,hx⟩
  refine ⟨x,y,?_,?_,hxy,hrep.symm,hex ▸ hfy,hey ▸ hfx⟩
  · rw [←he]; simp
  · rw [←he]; simp

lemma collision_le_pairing {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (F : Finset V → Prop) (s : Finset V) :
    collisionMass w F s ≤ EdgeMixing.pairing (linkEdge w s)
      (EdgeMixing.chi (fun x => F (insert x s))) (EdgeMixing.chi (fun x => F (insert x s))) := by
  let term := fun x y => linkEdge w s x y * EdgeMixing.chi (fun x => F (insert x s)) x *
    EdgeMixing.chi (fun x => F (insert x s)) y
  have ht : ∀ x y, 0 ≤ term x y := by
    intro x y
    dsimp [term,EdgeMixing.chi]
    split_ifs <;> simp_all [linkEdge_nonneg hw]
  have hpoint (a : Finset V) : (if Collision F s a then w a else 0) ≤
      ∑ x : V, ∑ y : V, if a = insert x (insert y s) then term x y else 0 := by
    by_cases hc : Collision F s a
    · rw [ite_eq_left hc]
      obtain ⟨x,y,hx,hy,hxy,hrep,hFx,hFy⟩ := hc.reconstruct
      have hv : (if a = insert x (insert y s) then term x y else 0) = w a := by
        simp [hrep,term,EdgeMixing.chi,hFx,hFy,linkEdge,hx,hy,hxy]
      rw [←hv]
      apply (Finset.single_le_sum (fun y _ => by split_ifs; exact ht x y; rfl)
        (Finset.mem_univ y)).trans
      apply Finset.single_le_sum _ (Finset.mem_univ x)
      intro u _
      exact Finset.sum_nonneg (fun v _ => by split_ifs; exact ht u v; rfl)
    · rw [ite_eq_right hc]
      exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => by
        split_ifs; exact ht x y; rfl))
  calc
    collisionMass w F s ≤ ∑ a ∈ level (s.card+2),
      ∑ x : V, ∑ y : V, if a = insert x (insert y s) then term x y else 0 :=
        Finset.sum_le_sum (fun a _ => hpoint a)
    _ = ∑ x : V, ∑ y : V, ∑ a ∈ level (s.card+2),
        if a = insert x (insert y s) then term x y else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ ≤ ∑ x : V, ∑ y : V, term x y := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      simp only [Finset.sum_ite_eq']
      split_ifs
      · rfl
      · exact ht x y
    _ = _ := rfl

theorem localMixing_of_rayleigh {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (hray : ∀ s : Finset V, s.card+2 ≤ N → 0 < w s → EdgeMixing.Rayleigh (linkEdge w s) lam) :
    LocalMixing w N lam := by
  intro F s hs t ht hsmall
  have hnon : 0 ≤ (t+lam)*(N:ℝ)*starNorm w (s.card+1) s (indicator F) :=
    mul_nonneg (mul_nonneg (add_nonneg ht hlam) (Nat.cast_nonneg _))
      (starNorm_nonneg hw.nonneg _ _ _)
  by_cases hr : s.card+2 ≤ N
  · by_cases hpos : 0 < w s
    · have hcpos : (0:ℝ) < (N-s.card-1:ℕ) := by exact_mod_cast (show 0 < N-s.card-1 by omega)
      have hvpos : 0 < EdgeMixing.volume (linkEdge w s) := by
        rw [linkEdge_volume hw]
        exact mul_pos (mul_pos hcpos (by exact_mod_cast (show 0 < N-s.card by omega))) hpos
      have hm : EdgeMixing.selected (linkEdge w s) (fun x => F (insert x s)) ≤
          t*EdgeMixing.volume (linkEdge w s) := by
        rw [linkEdge_selected hw,linkEdge_volume hw]
        nlinarith [mul_le_mul_of_nonneg_left hsmall hcpos.le]
      have hh := EdgeMixing.small_set (linkEdge w s) (linkEdge_nonneg hw.nonneg s)
        (linkEdge_symm w s) hvpos hlam (hray s hr hpos) (fun x => F (insert x s)) hm
      apply (collision_le_pairing hw.nonneg F s).trans
      apply hh.trans
      rw [linkEdge_selected hw]
      have hcN : (N-s.card-1:ℕ) ≤ N := by omega
      have hcr : ((N-s.card-1:ℕ):ℝ) ≤ N := by exact_mod_cast hcN
      have hn := starNorm_nonneg hw.nonneg (s.card+1) s (indicator F)
      nlinarith [mul_le_mul_of_nonneg_right hcr (mul_nonneg (add_nonneg ht hlam) hn)]
    · have hz : w s = 0 := le_antisymm (le_of_not_gt hpos) (hw.nonneg s)
      have hzero : collisionMass w F s = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        split_ifs with hc
        · obtain ⟨x,y,hx,hy,hxy,hrep,hFx,hFy⟩ := hc.reconstruct
          exact hw.weight_eq_zero_of_base (hrep ▸
            (Finset.subset_insert y s).trans (Finset.subset_insert x (insert y s))) hz
        · rfl
      rw [hzero]
      exact hnon
  · have hzero : collisionMass w F s = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hah := mem_level.mp ha
      split_ifs
      · exact hw.vanish a (by omega)
      · rfl
    rw [hzero]
    exact hnon

end CoboundaryExpanders.FatLadders

end

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.EdgeMixing

section
variable {V W : Type} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable

def action (e : V → V → ℝ) (f : V → ℝ) (x : V) : ℝ := (∑ y,e x y*f y)/mass e x
abbrev Active (e : V → V → ℝ) := {x : V // 0 < mass e x}
def Connected (e : V → V → ℝ) : Prop :=
  ∀ x y : Active e, Relation.ReflTransGen (fun a b : Active e => 0 < e a.val b.val) x y

lemma edge_le_mass {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) (x y : V) : e x y ≤ mass e x := by
  exact Finset.single_le_sum (fun z _ => he x z) (Finset.mem_univ y)
lemma edge_zero_of_nonactive {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) {x : V}
    (hx : ¬0 < mass e x) (y : V) : e x y = 0 :=
  le_antisymm ((edge_le_mass he x y).trans (not_lt.mp hx)) (he x y)

def activeEmbedding (e : V → V → ℝ) (he : ∀ x y,0 ≤ e x y) :
    Embedding (fun x y : Active e => e x.val y.val) e where
  vertex := Subtype.val
  injective := Subtype.val_injective
  edge_eq := fun _ _ => rfl
  outside_zero := by
    intro x hx y
    exact edge_zero_of_nonactive he (fun h => hx ⟨⟨x,h⟩,rfl⟩) y

def activeGraph (e : V → V → ℝ) (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) : Spectral.WeightedGraph (Active e) where
  edge := fun x y => e x.val y.val
  nonneg := fun x y => he x.val y.val
  symm := fun x y => hs x.val y.val
  row_pos := by
    intro x
    have hm := (activeEmbedding e he).mass_map hs x
    change mass (fun x y : Active e => e x.val y.val) x > 0
    rw [←hm]
    exact x.property

lemma active_action (e : V → V → ℝ) (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) (f : Active e → ℝ) (x : Active e) :
    action e ((activeEmbedding e he).extend f) x.val = (activeGraph e he hs).action f x := by
  let M := activeEmbedding e he
  change (∑ y,e x.val y*M.extend f y)/mass e x.val =
    (∑ y : Active e,e x.val y.val*f y)/(activeGraph e he hs).mass x
  have hz (y : V) (hy : y ∉ Set.range M.vertex) : e x.val y*M.extend f y = 0 := by
    rw [hs,M.outside_zero y hy,zero_mul]
  rw [sum_embedding M.vertex M.injective _ hz]
  have hm := M.mass_map hs x
  change mass e x.val = (activeGraph e he hs).mass x at hm
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [M.extend_map]
  rfl

theorem trickle {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) (hs : ∀ x y,e x y = e y x)
    (hc : Connected e) {lam : ℝ} (hlam : lam < 1)
    (hloc : ∀ f : V → ℝ, pairing e f f ≤ lam*energy e f+(1-lam)*energy e (action e f)) :
    Rayleigh e (lam/(1-lam)) := by
  let M := activeEmbedding e he
  by_cases hne : Nonempty (Active e)
  · let := hne
    let G := activeGraph e he hs
    apply M.push hs
    intro f hf
    change G.pairing f f ≤ (lam/(1-lam))*G.energy f
    apply G.trickle hc hlam _ f hf
    intro g
    have h := hloc (M.extend g)
    rw [M.pairing_pull hs,M.energy_pull hs,M.extend_comp,M.energy_pull hs] at h
    have hg : action e (M.extend g) ∘ M.vertex = G.action g := by
      funext x
      exact active_action e he hs g x
    rw [hg] at h
    exact h
  · have hzero (x y : V) : e x y = 0 :=
      M.outside_zero x (by rintro ⟨z,hz⟩; exact hne ⟨z⟩) y
    intro f hf
    simp only [pairing,energy,mass,hzero,zero_mul,Finset.sum_const_zero,mul_zero,le_refl]

end

variable {V : Type} [Fintype V]
lemma energy_sub_const (e : V → V → ℝ) (f : V → ℝ) (a : ℝ) :
    energy e (fun x => f x-a) = energy e f - 2*a*(∑ x,mass e x*f x)+a^2*(∑ x,mass e x) := by
  simp only [energy,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring
lemma pairing_sub_const (e : V → V → ℝ) (hs : ∀ x y,e x y = e y x)
    (f : V → ℝ) (a : ℝ) :
    pairing e (fun x => f x-a) (fun x => f x-a) =
      pairing e f f - 2*a*(∑ x,mass e x*f x)+a^2*(∑ x,mass e x) := by
  have he : pairing e (fun x => f x-a) (fun x => f x-a) = pairing e f f -
      a*(∑ x,∑ y,e x y*f x)-a*(∑ x,∑ y,e x y*f y)+a^2*(∑ x,mass e x) := by
    simp only [pairing,mass,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hr : (∑ x,∑ y,e x y*f y) = ∑ x,mass e x*f x := by
    rw [Finset.sum_comm]
    simp only [mass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hs]
  rw [he,hr]
  simp only [←Finset.sum_mul]
  change pairing e f f-a*(∑x,mass e x*f x)-a*(∑x,mass e x*f x)+_ = _
  ring

lemma centered_bound {e : V → V → ℝ} (hs : ∀ x y,e x y = e y x)
    {lam : ℝ} (h : Rayleigh e lam) (f : V → ℝ) (a : ℝ)
    (ha : (∑ x,mass e x*f x) = (∑ x,mass e x)*a) :
    pairing e f f ≤ lam*energy e f+(1-lam)*(∑ x,mass e x)*a^2 := by
  have hz : (∑ x,mass e x*(f x-a)) = 0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    rw [ha]; ring
  have hh := h (fun x => f x-a) hz
  rw [energy_sub_const,pairing_sub_const e hs,ha] at hh
  nlinarith [hh]

lemma mass_mul_action {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) (f : V → ℝ) (x : V) :
    mass e x * action e f x = ∑y,e x y*f y := by
  by_cases hx : mass e x = 0
  · have hz (y : V) : e x y = 0 := edge_zero_of_nonactive he (by rw [hx]; exact lt_irrefl _) y
    simp [hx,hz]
  · exact mul_div_cancel₀ _ hx

theorem triangle_moment {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) (d : V → V → V → ℝ)
    (hd : ∀ x y z,d x y z = d x z y) {c : ℝ} (hc : 0 < c)
    (hm : ∀ x y,mass (d x) y = c*e x y)
    (ht : ∀ y z,(∑ x,d x y z) = c*e y z)
    {lam : ℝ} (hr : ∀ x,Rayleigh (d x) lam) (f : V → ℝ) :
    pairing e f f ≤ lam*energy e f+(1-lam)*energy e (action e f) := by
  have hl (x : V) : pairing (d x) f f ≤ lam*energy (d x) f+
      (1-lam)*c*mass e x*(action e f x)^2 := by
    have hv : (∑y,mass (d x) y) = c*mass e x := by
      simp only [hm]
      rw [←Finset.mul_sum]
      rfl
    have hmean : (∑y,mass (d x) y*f y) = (∑y,mass (d x) y)*action e f x := by
      rw [hv]
      simp only [hm,mul_assoc,←Finset.mul_sum,mass_mul_action he]
    have h := centered_bound (hd x) (hr x) f (action e f x) hmean
    simpa only [hv,mul_assoc] using h
  have hp : (∑x,pairing (d x) f f) = c*pairing e f f := by
    simp only [pairing]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun x z => d x _ z*f _*f z)]
    simp only [←Finset.sum_mul,ht,Finset.mul_sum,mul_assoc]
  have hen : (∑x,energy (d x) f) = c*energy e f := by
    simp only [energy,hm]
    rw [Finset.sum_comm]
    simp only [←Finset.sum_mul,←Finset.mul_sum]
    unfold mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [show (∑x,e x y) = ∑x,e y x by apply Finset.sum_congr rfl; intro x _; rw [hs]]
    ring
  have ha : (∑x,(1-lam)*c*mass e x*(action e f x)^2) =
      c*(1-lam)*energy e (action e f) := by
    simp only [energy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hl x)
  rw [hp,Finset.sum_add_distrib,←Finset.mul_sum,hen,ha] at h
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith [h]

theorem triangle_trickle {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) (hconn : Connected e) (d : V → V → V → ℝ)
    (hd : ∀ x y z,d x y z = d x z y) {c : ℝ} (hc : 0 < c)
    (hm : ∀ x y,mass (d x) y = c*e x y)
    (ht : ∀ y z,(∑ x,d x y z) = c*e y z)
    {lam : ℝ} (hlam : lam < 1) (hr : ∀ x,Rayleigh (d x) lam) :
    Rayleigh e (lam/(1-lam)) :=
  trickle he hs hconn hlam (triangle_moment he hs d hd hc hm ht hr)
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.FatLadders

section
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def triangle (w : Finset V → ℝ) (s : Finset V) (x y z : V) : ℝ :=
  if x ∉ s then linkEdge w (insert x s) y z else 0
omit [Fintype V] in
lemma triangle_cycle (w : Finset V → ℝ) (s : Finset V) (x y z : V) :
    triangle w s x y z = triangle w s y z x := by
  unfold triangle linkEdge
  simp only [Finset.mem_insert]
  split_ifs <;> simp_all [Finset.insert_comm,ne_comm]
omit [Fintype V] in
lemma triangle_symm (w : Finset V → ℝ) (s : Finset V) (x y z : V) :
    triangle w s x y z = triangle w s x z y := by
  unfold triangle
  rw [linkEdge_symm]
lemma triangle_mass {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (x y : V) :
    EdgeMixing.mass (triangle w s x) y = (N-s.card-2:ℕ)*linkEdge w s x y := by
  by_cases hx : x ∈ s
  · simp [EdgeMixing.mass,triangle,linkEdge,hx]
  · have he : triangle w s x = linkEdge w (insert x s) := by funext a b; simp [triangle,hx]
    rw [he,linkEdge_mass hw,Finset.card_insert_of_notMem hx]
    have hnat : N-(s.card+1)-1 = N-s.card-2 := by omega
    rw [hnat]
    by_cases hy : y ∈ s
    · simp [linkEdge,hy]
    · by_cases hxy : x = y
      · subst y; simp [linkEdge]
      · simp [linkEdge,hx,hy,hxy,Ne.symm hxy,Finset.insert_comm]
lemma triangle_sum {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (y z : V) :
    (∑x,triangle w s x y z) = (N-s.card-2:ℕ)*linkEdge w s y z := by
  simp_rw [triangle_cycle w s _ y z]
  exact triangle_mass hw s y z
lemma linkEdge_zero {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {s : Finset V} (hz : w s = 0) : linkEdge w s = 0 := by
  funext x y
  unfold linkEdge
  split_ifs
  · exact hw.weight_eq_zero_of_base ((Finset.subset_insert y s).trans (Finset.subset_insert x _)) hz
  · rfl

theorem link_trickle {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (hrank : s.card+3 ≤ N)
    (hc : EdgeMixing.Connected (linkEdge w s)) {lam : ℝ} (hlam : lam < 1)
    (hray : ∀ x, x ∉ s → 0 < w (insert x s) →
      EdgeMixing.Rayleigh (linkEdge w (insert x s)) lam) :
    EdgeMixing.Rayleigh (linkEdge w s) (lam/(1-lam)) := by
  apply EdgeMixing.triangle_trickle (linkEdge_nonneg hw.nonneg s) (linkEdge_symm w s) hc
    (triangle w s) (triangle_symm w s) (by exact_mod_cast (show 0 < N-s.card-2 by omega))
    (triangle_mass hw s) (triangle_sum hw s) hlam
  intro x
  by_cases hx : x ∈ s
  · intro f hf
    simp [EdgeMixing.pairing,EdgeMixing.energy,EdgeMixing.mass,triangle,hx]
  · have he : triangle w s x = linkEdge w (insert x s) := by funext a b; simp [triangle,hx]
    rw [he]
    by_cases hp : 0 < w (insert x s)
    · exact hray x hx hp
    · have hz : w (insert x s) = 0 := le_antisymm (not_lt.mp hp) (hw.nonneg _)
      rw [linkEdge_zero hw hz]
      intro f hf
      simp [EdgeMixing.pairing,EdgeMixing.energy,EdgeMixing.mass]
end

variable {V : Type} [Fintype V] [DecidableEq V]
theorem link_trickle_double {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (hrank : s.card+3 ≤ N)
    (hc : EdgeMixing.Connected (linkEdge w s)) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hray : ∀ x, x ∉ s → 0 < w (insert x s) →
      EdgeMixing.Rayleigh (linkEdge w (insert x s)) (lam/2)) :
    EdgeMixing.Rayleigh (linkEdge w s) lam := by
  apply EdgeMixing.rayleigh_mono (linkEdge_nonneg hw.nonneg s) (link_trickle hw s hrank hc (by linarith) hray)
  apply (div_le_iff₀ (by linarith : 0 < 1-lam/2)).mpr
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

theorem all_link_rayleigh {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hc : ∀ s : Finset V, s.card+3 ≤ N → 0 < w s → EdgeMixing.Connected (linkEdge w s))
    (htop : ∀ s : Finset V, s.card+2 = N → 0 < w s →
      EdgeMixing.Rayleigh (linkEdge w s) (eps / 2^(N-2))) :
    ∀ s : Finset V, s.card+2 ≤ N → 0 < w s → EdgeMixing.Rayleigh (linkEdge w s) eps := by
  have main : ∀ r : ℕ, ∀ s : Finset V, N-s.card = r → s.card+2 ≤ N → 0 < w s →
      EdgeMixing.Rayleigh (linkEdge w s) (eps / 2^s.card) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro s heq hr hs
      by_cases ht : s.card+2 = N
      · have hcard : s.card = N-2 := by omega
        simpa only [hcard] using htop s ht hs
      · have hr3 : s.card+3 ≤ N := by omega
        have hp : (1:ℝ) ≤ 2^s.card := one_le_pow₀ (by norm_num)
        apply link_trickle_double hw s hr3 (hc s hr3 hs) (div_nonneg h0 (by positivity))
          ((div_le_self h0 hp).trans h1)
        intro x hx hxp
        have hc' : (insert x s).card = s.card+1 := Finset.card_insert_of_notMem hx
        have hi : N-(insert x s).card < r := by rw [hc']; omega
        have hh := ih (N-(insert x s).card) hi (insert x s) rfl (by rw [hc']; omega) hxp
        simpa only [hc',pow_succ,div_mul_eq_div_div] using hh
  intro s hr hs
  apply EdgeMixing.rayleigh_mono (linkEdge_nonneg hw.nonneg s) (main _ s rfl hr hs)
  exact div_le_self h0 (one_le_pow₀ (by norm_num))
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.InfiniteChains.FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable
lemma cofaces_chamberWeight (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) :
    FatLadders.chamberWeight (fun t : ↥(level X N) => t.val) (fun _ => (1:ℝ)) =
      fun s => (cofaces X N s : ℝ) := by
  funext s
  unfold FatLadders.chamberWeight cofaces
  dsimp only
  calc
    _ = ∑ t ∈ level X N, if s ⊆ t then (1:ℝ) else 0 :=
      Finset.sum_coe_sort (level X N) (fun t => if s ⊆ t then (1:ℝ) else 0)
    _ = _ := Finset.sum_boole _ _

lemma cofaces_balanced (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) :
    FatLadders.Balanced (fun s => (cofaces X N s : ℝ)) N := by
  rw [←cofaces_chamberWeight X N]
  exact FatLadders.chamberWeight_balanced _ _ N
    (fun t => ((mem_level X N t.val).mp t.property).2) (fun _ => by norm_num)

lemma linkEdge_eq (X : CoboundaryExpanders.InfiniteChains.Complex V) {N : ℕ} {s : Finset V} (hs : s ∈ X.faces)
    (hN : s.card ≤ N) :
    FatLadders.linkEdge (fun t => (cofaces X N t : ℝ)) s = edge (X.faceLink s hs) (N-s.card) := by
  funext x y
  by_cases hx : x ∈ s
  · have hf : ({x}:Finset V) ∉ (X.faceLink s hs).faces := by
      intro h
      exact Finset.disjoint_left.mp h.1 hx (Finset.mem_singleton_self x)
    simp [FatLadders.linkEdge,hx,edge_zero_of_not_face _ _ hf]
  by_cases hy : y ∈ s
  · have hf : ({y}:Finset V) ∉ (X.faceLink s hs).faces := by
      intro h
      exact Finset.disjoint_left.mp h.1 hy (Finset.mem_singleton_self y)
    rw [edge_symm _ _ x y,edge_zero_of_not_face _ _ hf]
    simp [FatLadders.linkEdge,hy]
  have hd : Disjoint s {x,y} := by simp [hx,hy]
  simp only [FatLadders.linkEdge,hx,hy,not_false_eq_true,true_and,edge]
  split_ifs
  · rw [cofaces_link X hs hN hd]
    congr 2
    ext z
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  · rfl
end CoboundaryExpanders.InfiniteChains.FiniteWeights

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]
lemma FiniteWeights.active_face (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) (x : V)
    (hx : 0 < EdgeMixing.mass (edge X N) x) : ({x}:Finset V) ∈ X.faces := by
  by_contra h
  have hz : EdgeMixing.mass (edge X N) x = 0 := by
    simp only [EdgeMixing.mass,edge_zero_of_not_face X N h,Finset.sum_const_zero]
  rw [hz] at hx
  exact (lt_irrefl _) hx
lemma FiniteWeights.edge_pos {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {x y : V}
    (hxy : x ≠ y) (hface : ({x,y}:Finset V) ∈ X.faces) : 0 < edge X N x y := by
  rw [edge,ite_eq_left hxy]
  exact_mod_cast cofaces_pos hP hface

lemma Cone.VertexPath.toActive {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} (hP : Pure X N) {x y : V}
    (hpath : VertexPath X x y) (hx : 0 < EdgeMixing.mass (edge X N) x)
    (hy : 0 < EdgeMixing.mass (edge X N) y) :
    Relation.ReflTransGen (fun a b : EdgeMixing.Active (edge X N) => 0 < edge X N a.val b.val)
      ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hpath hbc ih =>
    by_cases he : b = c
    · subst c
      exact ih hy
    · have hp := edge_pos hP he hbc
      have hb : 0 < EdgeMixing.mass (edge X N) b := hp.trans_le (EdgeMixing.edge_le_mass (edge_nonneg X N) b c)
      exact (ih hb).tail hp

theorem Cone.BoundedCone.spectralConnected {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R N : ℕ}
    (H : BoundedCone X n R) (hn : 1 ≤ n) (hP : Pure X N) :
    EdgeMixing.Connected (edge X N) := by
  intro x y
  exact (H.vertexPath hn x.val y.val (active_face X N x.val x.property)
    (active_face X N y.val y.property)).toActive hP x.property y.property
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains InfiniteChains.Cone InfiniteChains.FiniteWeights
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma spectralConnected_of_generate [Fintype (Vertex H)] {N : ℕ} (hp : Pure (complex H) N)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (base : I) :
    EdgeMixing.Connected (edge (complex H) N) := by
  intro x y
  exact (vertexPath_of_generate H hgen base x.val y.val).toActive hp x.property y.property
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction

section
open Elementary
variable (p n : ℕ) [Fact p.Prime]

def cycleGenerated (hn : 1 ≤ n) : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  Subgroup.closure (Set.range (cycleRoot p n hn))

omit [Fact p.Prime] in
theorem cycleRoot_mem_generated (hn : 1 ≤ n) (j : Fin (n + 1)) :
    cycleRoot p n hn j ∈ cycleGenerated p n hn :=
  Subgroup.subset_closure ⟨j, rfl⟩

theorem cycleGenerated_le_U (hn : 1 ≤ n) : cycleGenerated p n hn ≤ U p (n + 1) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact cycleRoot_mem_U p n hn j

omit [Fact p.Prime] in
theorem upper_adjacent_mem_generated (hn : 1 ≤ n) (i j : Fin (n + 1))
    (hij : i.val + 1 = j.val) :
    E (show i ≠ j by intro he; subst j; omega) (1 : R p) ∈ cycleGenerated p n hn := by
  have hj : j ≠ 0 := by intro he; subst j; simp at hij
  have hs : edgeSource n j = i := by
    apply Fin.ext
    simp only [edgeSource, dite_eq_right hj, Fin.val_mk]
    omega
  simpa only [cycleRoot, ite_eq_right hj, hs] using cycleRoot_mem_generated p n hn j

omit [Fact p.Prime] in
theorem upper_one_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i < j) :
    E hij.ne (1 : R p) ∈ cycleGenerated p n hn :=
  E_upper_one_mem _ (upper_adjacent_mem_generated p n hn) hij

omit [Fact p.Prime] in
theorem lower_X_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : j < i) :
    E hij.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
  have hlast0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  have hbase : E hlast0 (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    simpa [cycleRoot, edgeSource, E] using
      cycleRoot_mem_generated p n hn 0
  have hlastj : j < Fin.last n := by change j.val < n; have := i.isLt; omega
  have hlast : E hlastj.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    by_cases hj : j = 0
    · subst j; exact hbase
    · have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj
      simpa only [mul_one] using E_path_mem (cycleGenerated p n hn)
        hlast0 h0j.ne hlastj.ne.symm hbase (upper_one_mem_generated p n hn h0j)
  by_cases hi : i = Fin.last n
  · subst i; exact hlast
  · have hilast : i < Fin.last n := by change i.val < n; have := i.isLt; have := Fin.ext_iff.not.mp hi; simp only [Fin.val_last] at this; omega
    simpa only [one_mul] using E_path_mem (cycleGenerated p n hn)
      hilast.ne hlastj.ne.symm hij.ne.symm (upper_one_mem_generated p n hn hilast) hlast

omit [Fact p.Prime] in
theorem X_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) :
    E hij (Polynomial.X : R p) ∈ cycleGenerated p n (by omega) := by
  have hn1 : 1 ≤ n := by omega
  by_cases hji : j < i
  · exact lower_X_mem_generated p n hn1 hji
  have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = Fin.last n
    · subst j
      let k : Fin (n + 1) := ⟨1, by omega⟩
      have h0k : (0 : Fin (n + 1)) < k := by change (0 : ℕ) < 1; omega
      have hklast : k < Fin.last n := by change 1 < n; omega
      have hk0 := lower_X_mem_generated p n hn1 h0k
      have h0last := upper_one_mem_generated p n hn1 hij'
      have hklastX : E hklast.ne (Polynomial.X : R p) ∈ cycleGenerated p n hn1 := by
        simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
          h0k.ne.symm hij'.ne hklast.ne hk0 h0last
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0k.ne hklast.ne hij (upper_one_mem_generated p n hn1 h0k) hklastX
    · have hjlast : j < Fin.last n := by
        change j.val < n
        have := j.isLt
        have := Fin.ext_iff.not.mp hj
        simp only [Fin.val_last] at this
        omega
      have h0last : (0 : Fin (n + 1)) < Fin.last n := by change 0 < n; omega
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0last.ne hjlast.ne.symm hij (upper_one_mem_generated p n hn1 h0last)
        (lower_X_mem_generated p n hn1 hjlast)
  · have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    have h0j : (0 : Fin (n + 1)) < j := h0i.trans hij'
    simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
      h0i.ne.symm h0j.ne hij (lower_X_mem_generated p n hn1 h0i)
      (upper_one_mem_generated p n hn1 h0j)

omit [Fact p.Prime] in
theorem X_pow_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) (r : ℕ) :
    E hij (Polynomial.X ^ (r + 1) : R p) ∈ cycleGenerated p n (by omega) := by
  induction r generalizing i j with
  | zero => simpa only [zero_add, pow_one] using X_mem_generated p n hn hij
  | succ r ih =>
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    simpa only [pow_succ] using E_path_mem (cycleGenerated p n (by omega))
      hki.symm hkj hij (ih hki.symm) (X_mem_generated p n hn hkj)

theorem scalar_root_mem (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j)
    {f : R p} (hf : E hij f ∈ cycleGenerated p n hn) (c : ZMod p) :
    E hij (Polynomial.C c * f) ∈ cycleGenerated p n hn := by
  have hc : Polynomial.C c = (c.val : R p) := by
    calc Polynomial.C c = Polynomial.C (c.val : ZMod p) :=
           congrArg Polynomial.C (ZMod.natCast_zmod_val c).symm
         _ = _ := map_natCast Polynomial.C _
  rw [hc, E_natCast_mul]
  exact (cycleGenerated p n hn).pow_mem hf _

theorem upper_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i < j) (f : R p) : E hij.ne f ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    change Matrix.SpecialLinearGroup.transvection hij.ne (f + g) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    apply scalar_root_mem
    cases r with
    | zero => simpa using upper_one_mem_generated p n (by omega) hij
    | succ r => exact X_pow_mem_generated p n hn hij.ne r

theorem X_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i ≠ j) (f : R p) :
    E hij (Polynomial.X * f) ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add]
    change Matrix.SpecialLinearGroup.transvection hij (_ + _) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [mul_left_comm, ← pow_succ']
    exact scalar_root_mem p n (by omega) hij (X_pow_mem_generated p n hn hij r) c

end

open Elementary
variable (p n m : ℕ) [Fact p.Prime]

def residue (hm : 1 ≤ m) : Trunc p m →+* ZMod p :=
  Ideal.Quotient.lift (powerIdeal p m) (Polynomial.evalRingHom 0) (by
    change powerIdeal p m ≤ RingHom.ker (Polynomial.evalRingHom (R := ZMod p) 0)
    apply Ideal.span_le.mpr
    intro f hf
    have hf' : f = Polynomial.X ^ m := by simpa using hf
    subst f
    simp [show m ≠ 0 by omega])

@[simp] theorem residue_mk (hm : 1 ≤ m) (f : R p) :
    residue p m hm (Ideal.Quotient.mk (powerIdeal p m) f) = f.eval 0 := rfl

theorem residue_one_isUnit (hm : 1 ≤ m) (a : Trunc p m)
    (ha : residue p m hm a = 1) : IsUnit a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hf : (f - 1).eval 0 = 0 := by simpa using sub_eq_zero.mpr ha
  have hdiv : Polynomial.X ∣ f - 1 := Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hf)
  obtain ⟨b, hb⟩ := hdiv
  have he : Ideal.Quotient.mk (powerIdeal p m) f - 1 =
      tbar p m * Ideal.Quotient.mk (powerIdeal p m) b := by
    simpa only [map_sub, map_one, map_mul, tbar] using congrArg (Ideal.Quotient.mk (powerIdeal p m)) hb
  have hn : IsNilpotent (Ideal.Quotient.mk (powerIdeal p m) f - 1) := by
    rw [he]
    refine ⟨m, ?_⟩
    rw [mul_pow, tbar_pow, zero_mul]
  simpa only [sub_add_cancel] using hn.isUnit_add_one

theorem map_E {A B : Type*} [CommRing A] [CommRing B] {a : ℕ}
    (φ : A →+* B) {i j : Fin a} (hij : i ≠ j) (c : A) :
    Matrix.SpecialLinearGroup.map φ (E hij c) = E hij (φ c) := by
  exact map_transvection φ hij c

def truncatedIwahori (hm : 1 ≤ m) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m)) :=
  (upperUnitriangular p (n + 1)).comap (Matrix.SpecialLinearGroup.map (residue p m hm))

theorem truncatedIwahori_entries (hm : 1 ≤ m)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m))
    (hg : g ∈ truncatedIwahori p n m hm) (i j : Fin (n + 1)) (hji : j ≤ i) :
    residue p m hm (g i j) = if i = j then 1 else 0 := by
  have := hg i j hji
  simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.one_apply] using this

theorem reduction_mem_truncatedIwahori (hm : 1 ≤ m)
    {g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)} (hg : g ∈ U p (n + 1)) :
    Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) g ∈
      truncatedIwahori p n m hm := by
  intro i j hji
  have := hg i j hji
  simpa [evalZero, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] using this

def reducedGenerated (hn : 1 ≤ n) :=
  (cycleGenerated p n hn).map (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)))

theorem reducedGenerated_le (hn : 1 ≤ n) (hm : 1 ≤ m) :
    reducedGenerated p n m hn ≤ truncatedIwahori p n m hm := by
  rintro _ ⟨g, hg, rfl⟩
  exact reduction_mem_truncatedIwahori p n m hm (cycleGenerated_le_U p n hn hg)

theorem reducedGenerated_roots (hn : 2 ≤ n) (hm : 1 ≤ m)
    (i j : Fin (n + 1)) (hij : i ≠ j) (c : Trunc p m)
    (hc : j < i → residue p m hm c = 0) :
    E hij c ∈ reducedGenerated p n m (by omega) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨E hij f, ?_, map_E _ hij f⟩
  by_cases hji : j < i
  · have hf : Polynomial.X ∣ f := Polynomial.X_dvd_iff.mpr (by
      have := hc hji
      simpa [Polynomial.coeff_zero_eq_eval_zero] using this)
    obtain ⟨b, rfl⟩ := hf
    exact X_polynomial_mem_generated p n hn hij b
  · exact upper_polynomial_mem_generated p n hn (lt_of_le_of_ne (le_of_not_gt hji) hij) f

theorem truncatedIwahori_eq_generated (hn : 2 ≤ n) (hm : 1 ≤ m) :
    truncatedIwahori p n m hm = reducedGenerated p n m (by omega) := by
  apply le_antisymm
  · exact iwahori_mem_of_roots (residue p m hm) _ _
      (reducedGenerated_le p n m (by omega) hm)
      (truncatedIwahori_entries p n m hm) (residue_one_isUnit p m hm)
      (reducedGenerated_roots p n m hn hm)
  · exact reducedGenerated_le p n m (by omega) hm

theorem quotient_locals_generate (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Subgroup.closure (⋃ i, (reducedLocalGroup p n (by omega) m i : Set (Gquot p (n + 1) m))) = ⊤ := by
  let K : Subgroup (Gquot p (n + 1) m) :=
    Subgroup.closure (⋃ i, (reducedLocalGroup p n (by omega) m i : Set (Gquot p (n + 1) m)))
  let e : Gquot p (n + 1) m →* Matrix.SpecialLinearGroup (Fin (n + 1)) (Trunc p m) :=
    QuotientGroup.kerLift (uReduction p (n + 1) m)
  have he : Function.Injective e := QuotientGroup.kerLift_injective _
  have hgen : reducedGenerated p n m (by omega) ≤ K.map e := by
    apply (Subgroup.map_le_iff_le_comap).mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨cut, hcut⟩ : ∃ cut : Fin (n + 1), cut ≠ j := by
      by_cases hj : j = 0
      · refine ⟨Fin.last n, ?_⟩
        rw [hj]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      · exact ⟨0, fun h => hj h.symm⟩
    let u : U p (n + 1) := ⟨cycleRoot p n (by omega) j, cycleRoot_mem_U p n (by omega) j⟩
    have hu : u ∈ uLocalGroup p n (by omega) cut :=
      Subgroup.subset_closure ⟨j, hcut.symm, rfl⟩
    have hq : QuotientGroup.mk' (uReduction p (n + 1) m).ker u ∈ K :=
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨cut, ⟨u, hu, rfl⟩⟩)
    exact ⟨_, hq, rfl⟩
  apply top_le_iff.mp
  intro q _
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hu := reduction_mem_truncatedIwahori p n m hm u.property
    rw [truncatedIwahori_eq_generated p n m hn hm] at hu
    obtain ⟨v, hv, hev⟩ := hgen hu
    have hveq : v = QuotientGroup.mk u := he hev
    exact hveq ▸ hv

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders
lemma sqrt_div_le_of_sq {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (h : 1 ≤ t^2*p) :
    Real.sqrt p/p ≤ t := by
  have hs := Real.sqrt_nonneg p
  have he := Real.sq_sqrt hp.le
  have hsq : 1 ≤ (t*Real.sqrt p)^2 := by simpa only [mul_pow,he] using h
  have hpos : 0 ≤ t*Real.sqrt p := mul_nonneg ht.le hs
  have hb : 1 ≤ t*Real.sqrt p := by nlinarith
  apply (div_le_iff₀ hp).mpr
  calc
    Real.sqrt p = 1*Real.sqrt p := by ring
    _ ≤ (t*Real.sqrt p)*Real.sqrt p := mul_le_mul_of_nonneg_right hb hs
    _ = t*p := by nlinarith [mul_assoc t (Real.sqrt p) (Real.sqrt p)]

theorem exists_spectral_threshold (r : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ Q : ℕ, ∀ p : ℕ, Q < p → Real.sqrt (p:ℝ)/(p:ℝ) ≤ eps/(2:ℝ)^r := by
  let t := eps/(2:ℝ)^r
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨Q,hQ⟩ := exists_nat_gt (1/t^2)
  refine ⟨Q,?_⟩
  intro p hp
  have hp' : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hb : 1/t^2 ≤ (p:ℝ) := hQ.le.trans (by exact_mod_cast hp.le)
  have hc : 1 ≤ t^2*(p:ℝ) := by
    have h := (div_le_iff₀ (sq_pos_of_pos ht)).mp hb
    simpa only [mul_comm] using h
  exact sqrt_div_le_of_sq hp' ht hc
end CoboundaryExpanders

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains FiniteWeights Cone
open scoped Pointwise
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I] (H : I → Subgroup G)
noncomputable instance vertexFintype : Fintype (Vertex H) := Fintype.ofFinite _

lemma finite_pure : Pure (complex H) (Fintype.card I) := by
  obtain ⟨hne,h⟩ := coset_pure H
  constructor
  · obtain ⟨t,ht,he⟩ := hne
    exact ⟨t,(mem_level _ _ _).mpr ⟨ht,he⟩⟩
  · intro s hs
    obtain ⟨t,ht,he,hst⟩ := h s hs
    exact ⟨t,(mem_level _ _ _).mpr ⟨ht,he⟩,hst⟩

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.InfiniteChains
open Cone FiniteWeights
variable {V : Type} [Fintype V] [DecidableEq V]

lemma FiniteWeights.linkEdge_empty (X : CoboundaryExpanders.InfiniteChains.Complex V) (N : ℕ) :
    FatLadders.linkEdge (fun t => (cofaces X N t : ℝ)) ∅ = edge X N := by
  funext x y
  simp [FatLadders.linkEdge,edge]

lemma TopSpectral.changeFintype {V : Type} [DecidableEq V] {fa : Fintype V}
    (fb : Fintype V) {X : CoboundaryExpanders.InfiniteChains.Complex V} {N : ℕ} {lam : ℝ}
    (ht : @TopSpectral V fa _ X N lam) : @TopSpectral V fb _ X N lam := by
  cases Subsingleton.elim fa fb
  exact ht

theorem mixing_of_top_cones {X : CoboundaryExpanders.InfiniteChains.Complex V} {N R : ℕ} (hp : Pure X N)
    (hc : EdgeMixing.Connected (edge X N)) (hcones : ProperLinkCones X N R)
    {eps lam : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (htop : TopSpectral X N lam) (hlam : lam ≤ eps/2^(N-2)) :
    FatLadders.LocalMixing (fun t => (cofaces X N t : ℝ)) N eps := by
  apply FatLadders.localMixing_of_rayleigh (cofaces_balanced X N) h0
  apply FatLadders.all_link_rayleigh (cofaces_balanced X N) h0 h1
  · intro s hr hs
    have hs' : s ∈ X.faces := (cofaces_pos_iff hp s).mp (by exact_mod_cast hs)
    by_cases he : s.Nonempty
    · rw [linkEdge_eq X hs' (by omega)]
      exact (hcones s he hs' (by omega)).some.spectralConnected (by omega) (pure_link hp hs')
    · have he' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      subst s
      rwa [linkEdge_empty X N]
  · intro s hr hs
    have hs' : s ∈ X.faces := (cofaces_pos_iff hp s).mp (by exact_mod_cast hs)
    rw [linkEdge_eq X hs' (by omega)]
    have he : N-s.card = 2 := by omega
    rw [he]
    exact EdgeMixing.rayleigh_mono (edge_nonneg _ _) (htop s hs' hr) hlam
end CoboundaryExpanders.InfiniteChains

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains Cone FiniteWeights
variable {G I : Type} [Group G] [Fintype G] [DecidableEq I] [Fintype I]
lemma coset_mixing (H : I → Subgroup G) {N R : ℕ} (hN : Fintype.card I = N)
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) (base : I)
    {eps lam : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hcones : ProperLinkCones (complex H) N R) (ht : TopSpectral (complex H) N lam)
    (hlam : lam ≤ eps / 2^(N-2)) :
    FatLadders.LocalMixing (fun t => (cofaces (complex H) N t : ℝ)) N eps := by
  have hP : Pure (complex H) N := hN ▸ finite_pure H
  exact mixing_of_top_cones hP (spectralConnected_of_generate H hP hgen base)
    hcones h0 h1 ht hlam
end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open InfiniteChains Cone FiniteWeights TypedCosetFaces

lemma actual_mixing_level (n : ℕ) (hn : 2 ≤ n) (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hm : 2 ≤ m) {R : ℕ} {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ 1)
    (hcones : ProperLinkCones (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) R)
    (hlam : Real.sqrt p / p ≤ eps / 2^(n+1-2)) :
    letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
    FatLadders.LocalMixing
      (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) t : ℝ)) (n+1) eps := by
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  have htop := actual_topSpectral n hn p m hm
  have ht := TopSpectral.changeFintype (vertexFintype (reducedLocalGroup p n (by omega) m)) htop
  exact coset_mixing (reducedLocalGroup p n (by omega) m) (Fintype.card_fin _)
    (quotient_locals_generate p n m hn (by omega)) 0 h0 h1 hcones
    ht hlam

lemma actual_mixing_mono (n : ℕ) (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime] (m : ℕ)
    {eps mu : ℝ} (h : eps ≤ mu) :
    letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
    FatLadders.LocalMixing
      (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) t : ℝ)) (n+1) eps →
    FatLadders.LocalMixing
      (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n hn m)) (n+1) t : ℝ)) (n+1) mu := by
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  intro hmix F s hs t ht hb
  apply (hmix F s hs t ht hb).trans
  apply mul_le_mul_of_nonneg_right _ (FatLadders.starNorm_nonneg (fun s => Nat.cast_nonneg _) _ _ _)
  exact mul_le_mul_of_nonneg_right (add_le_add_right h t) (Nat.cast_nonneg _)

theorem uniform_actual_mixing (n : ℕ) (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) :
    ∃ Q : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p → ∀ m : ℕ, 2 ≤ m →
      letI : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
      FatLadders.LocalMixing
        (fun t => (cofaces (TypedCosetFaces.complex (reducedLocalGroup p n (by omega) m)) (n+1) t : ℝ))
        (n+1) eps := by
  obtain ⟨Q₀,R,hcones⟩ := uniform_actual_proper_link_cones n (by omega)
  obtain ⟨Q₁,hspectral⟩ := exists_spectral_threshold (n+1-2) (lt_min heps zero_lt_one)
  refine ⟨max Q₀ Q₁,?_⟩
  intro p hp hq m hm
  exact actual_mixing_mono n (by omega) p m (min_le_left eps 1)
    (actual_mixing_level n hn p m hm (le_of_lt (lt_min heps zero_lt_one))
      (min_le_right eps 1) (hcones p hp ((le_max_left _ _).trans_lt hq) m hm)
      (hspectral p ((le_max_right _ _).trans_lt hq)))
end CoboundaryExpanders.Construction

end

end OAI
