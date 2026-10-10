import Mathlib
import OAI.Computability.MinUncut.Graphs.SignedGraph

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable
variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D]
variable {N : ℕ}

def output (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k) : MinUncut.Output where
  vertices := N
  adjacent u v := decide ((graph e).Adj (number.symm u) (number.symm v))
  symmetric u v := by simp only [decide_eq_decide]; exact (graph e).adj_comm _ _
  loopless u := by simp
  threshold := k
  threshold_pos := hk

def edgePair (e : D → Demand V) (number : Vertex V D ≃ Fin N) (p : EdgeIndex e) : Fin N × Fin N :=
  (Sym2.sortEquiv (Sym2.map number (edge e p))).val

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_sym (e : D → Demand V) (number : Vertex V D ≃ Fin N) (p : EdgeIndex e) :
    s((edgePair e number p).1,(edgePair e number p).2)=Sym2.map number (edge e p) :=
  Sym2.sortEquiv.symm_apply_apply _

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_injective (e : D → Demand V) (number : Vertex V D ≃ Fin N) :
    Function.Injective (edgePair e number) := by
  intro p q h
  apply edge_injective e
  apply Sym2.map.injective number.injective
  rw [← edgePair_sym,← edgePair_sym,h]

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_lt (e : D → Demand V) (number : Vertex V D ≃ Fin N) (p : EdgeIndex e) :
    (edgePair e number p).1 < (edgePair e number p).2 := by
  have hl := (Sym2.sortEquiv (Sym2.map number (edge e p))).property
  apply lt_of_le_of_ne hl
  intro he
  have hd : (Sym2.map number (edge e p)).IsDiag := by
    rw [← edgePair_sym,Sym2.mk_isDiag_iff]
    exact he
  exact ends_ne e p ((Sym2.isDiag_map number.injective).mp hd)

omit [Fintype V] in
lemma output_adjacent_iff (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (u v : Fin N) :
    (output e number k hk).adjacent u v=true ↔ ∃ p : EdgeIndex e, s(u,v)=Sym2.map number (edge e p) := by
  simp only [output,decide_eq_true_eq,graph,edgeSet,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    simpa using (congrArg (Sym2.map number) hp).symm
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    apply Sym2.map.injective number.injective
    simpa using hp.symm

omit [Fintype V] in
lemma output_forward_edge_iff (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (u v : Fin N) :
    (u<v ∧ (output e number k hk).adjacent u v=true) ↔ ∃ p : EdgeIndex e, edgePair e number p=(u,v) := by
  rw [output_adjacent_iff]
  constructor
  · rintro ⟨hu,p,hp⟩
    refine ⟨p,?_⟩
    unfold edgePair
    rw [← hp]
    simp [Sym2.sortEquiv,le_of_lt hu]
  · rintro ⟨p,hp⟩
    refine ⟨?_,p,?_⟩
    · simpa only [hp] using edgePair_lt e number p
    · rw [← edgePair_sym,hp]

omit [Fintype V] [Fintype D] [DecidableEq V] [DecidableEq D] in
lemma edgePair_mono (e : D → Demand V) (number : Vertex V D ≃ Fin N)
    (s : Fin N → Bool) (p : EdgeIndex e) :
    mono (s (edgePair e number p).1) (s (edgePair e number p).2)=
      mono (s (number (ends e p.val).1)) (s (number (ends e p.val).2)) := by
  have he := edgePair_sym e number p
  change s((edgePair e number p).1,(edgePair e number p).2)=s(number (ends e p.val).1,number (ends e p.val).2) at he
  rcases Sym2.eq_iff.mp he with h|h
  · rw [h.1,h.2]
  · rw [h.1,h.2]; simp only [mono,eq_comm]

omit [Fintype V] in
lemma output_uncut (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (s : Fin N → Bool) :
    (output e number k hk).uncut s=uncut e (s ∘ number) := by
  have he : (Finset.univ.filter fun uv : Fin N×Fin N =>
      uv.1<uv.2 ∧ (output e number k hk).adjacent uv.1 uv.2=true ∧ s uv.1=s uv.2)=
      (Finset.univ.filter fun p : EdgeIndex e => s (edgePair e number p).1=s (edgePair e number p).2).image (edgePair e number) := by
    ext uv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨hu,ha,hs⟩
      obtain ⟨p,hp⟩ := (output_forward_edge_iff e number k hk uv.1 uv.2).mp ⟨hu,ha⟩
      exact ⟨p,by simpa only [hp] using hs,hp⟩
    · rintro ⟨p,hs,hp⟩
      have hh := (output_forward_edge_iff e number k hk uv.1 uv.2).mpr ⟨p,hp⟩
      exact ⟨hh.1,hh.2,by simpa only [hp] using hs⟩
  unfold MinUncut.Output.uncut
  erw [he,Finset.card_image_of_injective _ (edgePair_injective e number)]
  change _=∑ p : EdgeIndex e, mono (s (number (ends e p.val).1)) (s (number (ends e p.val).2))
  simp_rw [← edgePair_mono]
  simp only [mono,Finset.card_filter]

lemma output_opt_le (G : MinUncut.Output) (s : Fin G.vertices → Bool) : G.opt ≤ G.uncut s := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)

lemma le_output_opt (G : MinUncut.Output) (r : ℕ) (h : ∀ s, r ≤ G.uncut s) : r ≤ G.opt := by
  apply Finset.le_min'
  intro x hx
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hx
  exact h s

omit [Fintype V] in
lemma output_yes (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (s : V → Bool) (h : totalFailure e s ≤ k) : (output e number k hk).opt ≤ k := by
  apply (output_opt_le _ ((extend e s) ∘ number.symm)).trans
  erw [output_uncut]
  have he : ((extend e s) ∘ number.symm) ∘ number=extend e s := by ext v; simp
  erw [he,uncut_extend]
  exact h

omit [Fintype V] in
lemma output_no (e : D → Demand V) (number : Vertex V D ≃ Fin N) (k : ℕ) (hk : 1 ≤ k)
    (R : ℕ) (h : ∀ s : V → Bool, R<totalFailure e s) : R<(output e number k hk).opt := by
  apply lt_of_lt_of_le (Nat.lt_succ_self R)
  apply le_output_opt
  intro s
  erw [output_uncut]
  exact (h (fun v => s (number (.inl v)))).trans_le (uncut_lower e (s ∘ number))
end MinUncut.PathRealization

open scoped BigOperators
namespace MinUncut.FiniteProof
open PathRealization
variable {E V : Type*} [Fintype E]

def multiplicity (D : ℕ) (w : ℚ) : ℕ := w.num.toNat*(D/w.den)

lemma multiplicity_cast {D : ℕ} {w : ℚ} (hw : 0≤w) (hD : w.den ∣ D) :
    (multiplicity D w:ℚ)=(D:ℚ)*w := by
  have hn : 0≤w.num := Rat.num_nonneg.mpr hw
  have hncast : (w.num.toNat:ℚ)=(w.num:ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn
  calc
    (multiplicity D w:ℚ)=(w.num:ℚ)*((D:ℚ)/(w.den:ℚ)) := by
      unfold multiplicity
      rw [Nat.cast_mul,Nat.cast_div_charZero hD,hncast]
    _ = (D:ℚ)*((w.num:ℚ)/(w.den:ℚ)) := by ring
    _ = (D:ℚ)*w := by rw [Rat.num_div_den]

abbrev UnitDemand (D : ℕ) (w : E → ℚ) := Σ e, Fin (multiplicity D (w e))

def expanded (D : ℕ) (w : E → ℚ) (d : E → Demand V) : UnitDemand D w → Demand V :=
  fun p => d p.1

lemma expanded_failure (D : ℕ) (w : E → ℚ) (d : E → Demand V) (y : V → Bool) :
    totalFailure (expanded D w d) y = ∑ e, multiplicity D (w e)*failure (d e) y := by
  simp [totalFailure,expanded,Fintype.sum_sigma]

lemma expanded_weight (D : ℕ) (w : E → ℚ) (hw : ∀ e, 0≤w e) (hD : ∀ e, (w e).den ∣ D)
    (d : E → Demand V) (y : V → Bool) :
    (totalFailure (expanded D w d) y:ℝ)=(D:ℝ)*∑ e, (w e:ℝ)*(failure (d e) y:ℝ) := by
  rw [expanded_failure]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have h : (multiplicity D (w e):ℝ)=(D:ℝ)*(w e:ℝ) := by
    exact_mod_cast multiplicity_cast (hw e) (hD e)
  rw [h,mul_assoc]

lemma expanded_card (D : ℕ) (w : E → ℚ) :
    Fintype.card (UnitDemand D w)=∑ e, multiplicity D (w e) := by
  simp [Fintype.card_sigma]

lemma expanded_card_cast (D : ℕ) (w : E → ℚ) (hw : ∀ e, 0≤w e) (hD : ∀ e, (w e).den ∣ D) :
    (Fintype.card (UnitDemand D w):ℚ)=(D:ℚ)*∑ e, w e := by
  rw [expanded_card,Nat.cast_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => multiplicity_cast (hw e) (hD e))


open scoped BigOperators
open PathRealization
attribute [local instance] Classical.propDecidable
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

lemma threshold_positive {D : ℕ} (hD : 0<D) : 1≤5*D := by omega

def rationalGraph (D : ℕ) (hD : 0<D) (w : E → ℚ) (d : E → Demand V) : MinUncut.Output :=
  output (expanded D w d) (Fintype.equivFin _) (5*D) (threshold_positive hD)

lemma rationalGraph_threshold (D : ℕ) (hD : 0<D) (w : E → ℚ) (d : E → Demand V) :
    (rationalGraph D hD w d).threshold=5*D := rfl

lemma rationalGraph_vertices (D : ℕ) (hD : 0<D) (w : E → ℚ) (d : E → Demand V) :
    (rationalGraph D hD w d).vertices=Fintype.card V+3*∑ e, multiplicity D (w e) := by
  simp [rationalGraph,output,Vertex,Fintype.card_sum,Fintype.card_prod,mul_comm]

lemma rationalGraph_yes (D : ℕ) (hD : 0<D) (w : E → ℚ) (hw : ∀ e, 0≤w e)
    (hden : ∀ e, (w e).den ∣ D) (d : E → Demand V) (y : V → Bool)
    (hc : (∑ e, (w e:ℝ)*(failure (d e) y:ℝ))≤9/2) :
    (rationalGraph D hD w d).opt≤(rationalGraph D hD w d).threshold := by
  apply output_yes
  have he := expanded_weight D w hw hden d y
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hh := mul_le_mul_of_nonneg_left hc hD'.le
  have hz : (totalFailure (expanded D w d) y:ℝ)≤5*D := by rw [he]; nlinarith
  exact_mod_cast hz

lemma rationalGraph_no {K : ℕ} (hK : 2≤K) (D : ℕ) (hD : 0<D) (w : E → ℚ)
    (hw : ∀ e, 0≤w e) (hden : ∀ e, (w e).den ∣ D) (d : E → Demand V)
    (hc : ∀ y, 8*(K:ℝ)-1/2 < ∑ e, (w e:ℝ)*(failure (d e) y:ℝ)) :
    K*(rationalGraph D hD w d).threshold < (rationalGraph D hD w d).opt := by
  apply output_no
  intro y
  have he := expanded_weight D w hw hden d y
  have hK' : (2:ℝ)≤K := by exact_mod_cast hK
  have hg : 5*(K:ℝ) < ∑ e, (w e:ℝ)*(failure (d e) y:ℝ) := lt_trans (by linarith) (hc y)
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hh := mul_lt_mul_of_pos_left hg hD'
  have hz : (K:ℝ)*(5*D) < (totalFailure (expanded D w d) y:ℝ) := by rw [he]; nlinarith
  exact_mod_cast hz

end MinUncut.FiniteProof

end

end OAI
