import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.EndpointPair

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma switch_denominator_bound (hinc : ∀ e, ∃ v, inc e v) (A : PM inc) :
    48 * (A.val.card.choose 2 : ℝ) ≤ 60 * (Fintype.card V : ℝ)^2 := by
  have hm := A.card_le_vertices hinc
  have hc : A.val.card.choose 2 ≤ (Fintype.card V)^2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hm 2)
  have hc' : (A.val.card.choose 2 : ℝ) ≤ (Fintype.card V : ℝ)^2 := by exact_mod_cast hc
  nlinarith [sq_nonneg (Fintype.card V : ℝ)]

omit [DecidableEq V] in
lemma safe_switch_elementary (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (K : ℝ) (hK : 1 ≤ K) (f : Finset E → ℝ) :
    (∑ A : PM inc, gibbs w A * ∑ B ∈ safeDestinations w K A, (f A.val-f B.val)^2) ≤
      60 * (Fintype.card V : ℝ)^2 * K^2 * switchDirichlet (inc := inc) w f := by
  classical
  simp only [switchDirichlet,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  let term (B : PM inc) := 60*(Fintype.card V : ℝ)^2*K^2 *
    (min (gibbs w A) (gibbs w B)*(f A.val-f B.val)^2 / (48*(A.val.card.choose 2 : ℝ)))
  change (∑ B ∈ safeDestinations w K A, gibbs w A*(f A.val-f B.val)^2) ≤
    ∑ B ∈ switchDestinations A, term B
  calc
    _ ≤ ∑ B ∈ safeDestinations w K A, term B := by
      apply Finset.sum_le_sum
      intro B hB
      have h : SafeSwitch w K A B := (Finset.mem_filter.mp hB).2
      have hd : 0 < 48 * (A.val.card.choose 2 : ℝ) := by
        have hc : 0 < A.val.card.choose 2 := Nat.choose_pos h.legal.two_le
        positivity
      have hn : 0 ≤ min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 :=
        mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)
      have h₁ := mul_le_mul_of_nonneg_right (h.min_capacity hw hK) (sq_nonneg (f A.val-f B.val))
      have h₂ := mul_le_mul_of_nonneg_left (scale_div_lower hn hd (switch_denominator_bound hinc A)) (sq_nonneg K)
      dsimp only [term]
      nlinarith only [h₁,h₂]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro B hB
        have h : SafeSwitch w K A B := (Finset.mem_filter.mp hB).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.legal⟩
      · intro B _ _
        have ha := le_of_lt (gibbs_pos w hw A)
        have hb := le_of_lt (gibbs_pos w hw B)
        dsimp only [term]
        positivity

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.card_pos {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    0 < A.val.card := by
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  exact Finset.card_pos.mpr ⟨e,by rw [hA]; simp⟩

omit [DecidableEq V] in
lemma color_elementary (w : E → ℝ) (hw : ∀ e, 0 < w e) (K : ℝ) (hK : 1 ≤ K)
    (hcomp : ∀ e f, ends e = ends f → w e ≤ K*w f) (f : Finset E → ℝ) :
    (∑ A : PM (fun e v => v ∈ ends e), gibbs w A *
      ∑ B ∈ colorDestinations ends A, (f A.val-f B.val)^2) ≤
      12 * (Fintype.card V : ℝ) * K * colorDirichlet ends w f := by
  classical
  have hinc (e : E) : ∃ v, v ∈ ends e := by
    induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
  simp only [colorDirichlet,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  apply Finset.sum_le_sum
  intro B hB
  have h : ColorChange ends A B := (Finset.mem_filter.mp hB).2
  have hd : 0 < 12 * (A.val.card : ℝ) := by have := h.card_pos ends; positivity
  have hb : 12 * (A.val.card : ℝ) ≤ 12 * (Fintype.card V : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_left 12 (A.card_le_vertices hinc))
  have hn : 0 ≤ min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 :=
    mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_right (h.min_capacity ends hw hK hcomp) (sq_nonneg (f A.val-f B.val))
  have h₂ := mul_le_mul_of_nonneg_left (scale_div_lower hn hd hb) (by linarith : 0 ≤ K)
  nlinarith only [h₁,h₂]

omit [Fintype E] in
lemma cycleSquare_common (f g : Finset E → ℝ) (A B S : Finset E) (hS : S ⊆ A ∩ B) :
    cycleSquare f g A B S = 0 := by
  have hSA : S ⊆ A := fun e he => (Finset.mem_inter.mp (hS he)).1
  have hSB : S ⊆ B := fun e he => (Finset.mem_inter.mp (hS he)).2
  simp only [cycleSquare,exchange,Finset.inter_eq_right.mpr hSA,Finset.inter_eq_right.mpr hSB,
    Finset.sdiff_union_of_subset hSA,Finset.sdiff_union_of_subset hSB,sub_self,zero_pow (by decide : 2 ≠ 0)]

omit [DecidableEq V] [Fintype E] in
lemma all_cycleSquare_sum (f g : Finset E → ℝ) (A B : PM inc) :
    (∑ S ∈ components (inc := inc) (A.val ∪ B.val), cycleSquare f g A.val B.val S) =
      ∑ S ∈ discrepancyComponents A B, cycleSquare f g A.val B.val S := by
  classical
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro S hS hnot
  have hcommon : S ⊆ A.val ∩ B.val := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hS,h⟩)
  exact cycleSquare_common f g _ _ _ hcommon

omit [DecidableEq V] in
lemma cycle_elementary (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (f g : Finset E → ℝ) :
    (∑ A : PM inc, ∑ B : PM inc, gibbs w A * gibbs w B *
      ∑ S ∈ components (inc := inc) (A.val ∪ B.val), cycleSquare f g A.val B.val S) ≤
      6 * (Fintype.card V : ℝ) * cycleDirichlet (inc := inc) w f g := by
  classical
  simp only [cycleDirichlet,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  apply Finset.sum_le_sum
  intro B _
  rw [← Finset.mul_sum,all_cycleSquare_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hcard : 0 < (discrepancyComponents A B).card := Finset.card_pos.mpr ⟨S,hS⟩
  have hd : (discrepancyComponents A B).card ≤ Fintype.card V :=
    (Finset.card_filter_le _ _).trans (components_card_le hinc _)
  have hb : 6 * ((discrepancyComponents A B).card : ℝ) ≤ 6 * (Fintype.card V : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 6 hd
  have hscale := scale_div_lower (sq_nonneg ((f A.val+g B.val)-(f (exchange A.val B.val S)+g (exchange B.val A.val S))))
    (by positivity : 0 < 6 * ((discrepancyComponents A B).card : ℝ)) hb
  have h := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B)))
  dsimp only [cycleSquare] at *
  nlinarith only [h]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.FiniteVariance

variable {Ω : Type*} [Fintype Ω]

noncomputable def variance (π f : Ω → ℝ) : ℝ :=
  ∑ x, π x * (f x - ∑ y, π y * f y)^2

lemma variance_eq_pair (π f : Ω → ℝ) (hπ : ∑ x, π x = 1) :
    variance π f = (∑ p : Ω × Ω, π p.1 * π p.2 * (f p.1-f p.2)^2) / 2 := by
  let m := ∑ y, π y * f y
  let s := ∑ y, π y * f y ^ 2
  have hl : variance π f = s-m^2 := by
    unfold variance
    change (∑ x, π x * (f x-m)^2) = s-m^2
    calc
      _ = ∑ x, (π x * f x^2 - 2*m*(π x*f x) + m^2*π x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = s-m^2 := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hπ]
        change s-2*m*m+m^2*1 = s-m^2
        ring
  have hr : (∑ p : Ω × Ω, π p.1 * π p.2 * (f p.1-f p.2)^2) = 2*(s-m^2) := by
    rw [Fintype.sum_prod_type]
    have hin (x : Ω) : (∑ y, π x*π y*(f x-f y)^2) = π x*f x^2-2*m*(π x*f x)+s*π x := by
      calc
        _ = ∑ y, ((π x*f x^2)*π y - (2*π x*f x)*(π y*f y) + π x*(π y*f y^2)) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hπ]
          change (π x*f x^2)*1-(2*π x*f x)*m+π x*s = _
          ring
    simp_rw [hin]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hπ]
    change s-2*m*m+s*1 = 2*(s-m^2)
    ring
  rw [hl,hr]
  ring

end MatchingFPRAS.FiniteVariance

namespace MatchingFPRAS

lemma energy_coefficient_bound {N D T : ℝ} (hN1 : 1 ≤ N) (hD : 1 ≤ D)
    (hT0 : 0 ≤ T) (htag : T ≤ (10*N)^30) :
    180*N^5*(1000*D)^6*T+72*N^4*(1000*D)^4*T+12*N^3*(1000*D) ≤
      ((10^4 : ℝ)*N*D)^100 := by
  let K := 1000*D
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hN0 : 0 ≤ N := by linarith
  have hDN : N ≤ N*D := by nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hD)]
  have hDD : D ≤ N*D := by nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (le_trans (by norm_num : (0:ℝ) ≤ 1) hD)]
  let B := (10^4 : ℝ)*N*D
  have hB : 3 ≤ B := by dsimp [B]; nlinarith
  have hNB : N ≤ B := by dsimp [B]; nlinarith
  have hKB : K ≤ B := by dsimp [B,K]; nlinarith
  have h10NB : 10*N ≤ B := by dsimp [B]; nlinarith
  have hTB : T ≤ B^30 := htag.trans (by gcongr)
  have h180 : (180:ℝ) ≤ B := by dsimp [B]; nlinarith
  have h72 : (72:ℝ) ≤ B := by linarith
  have h12 : (12:ℝ) ≤ B := by linarith
  have hb0 : 0 ≤ B := by linarith
  have hterm1 : 180*N^5*K^6*T ≤ B^42 := by
    calc
      _ ≤ B*B^5*B^6*B^30 := by gcongr
      _ = _ := by ring
  have hterm2 : 72*N^4*K^4*T ≤ B^39 := by
    calc
      _ ≤ B*B^4*B^4*B^30 := by gcongr
      _ = _ := by ring
  have hterm3 : 12*N^3*K ≤ B^5 := by
    calc
      _ ≤ B*B^3*B := by gcongr
      _ = _ := by ring
  have hp39 : B^39 ≤ B^42 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by omega)
  have hp5 : B^5 ≤ B^42 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by omega)
  have hcoef : 180*N^5*K^6*T+72*N^4*K^4*T+12*N^3*K ≤ B^100 := by
    calc
      _ ≤ 3*B^42 := by linarith
      _ ≤ B*B^42 := mul_le_mul_of_nonneg_right hB (pow_nonneg hb0 _)
      _ = B^43 := by ring
      _ ≤ B^100 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by omega)
  exact hcoef

end MatchingFPRAS

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

include hheight hstep hD hw hlo hlohi hbags hG

theorem pair_energy_inequality (hN : 2 ≤ Fintype.card V)
    (M : PM (BagEdge.Incident (bags := bags))) (f g : Finset (BagEdge bags) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    MatchingFPRAS.FiniteVariance.variance (gibbs (inc := BagEdge.Incident) wt) (fun A => f A.val) ≤
      ((10^4 : ℝ) * Fintype.card V * D)^100 *
        pairDirichlet (fun e : BagEdge bags => e.val.val.1) wt f g := by
  classical
  let wt := fun e => max lo (min hi (w e))
  have hwt (e : BagEdge bags) : 0 < wt e := lt_of_lt_of_le hlo (le_max_left _ _)
  let N : ℝ := Fintype.card V
  let K : ℝ := 1000*D
  let T : ℝ := Fintype.card (DemandTag (V := V) (E := BagEdge bags))
  let E := pairDirichlet (fun e : BagEdge bags => e.val.val.1) wt f g
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hE : 0 ≤ E := by
    exact add_nonneg (add_nonneg (switchDirichlet_nonneg wt hwt f)
      (colorDirichlet_nonneg _ wt hwt f)) (cycleDirichlet_nonneg wt hwt f g)
  have hsE : switchDirichlet (inc := BagEdge.Incident) wt f ≤ E :=
    (le_add_of_nonneg_right (colorDirichlet_nonneg (fun e : BagEdge bags => e.val.val.1) wt hwt f)).trans
      (le_add_of_nonneg_right (cycleDirichlet_nonneg wt hwt f g))
  have hcE : colorDirichlet (fun e : BagEdge bags => e.val.val.1) wt f ≤ E :=
    (le_add_of_nonneg_left (switchDirichlet_nonneg (inc := BagEdge.Incident) wt hwt f)).trans
      (le_add_of_nonneg_right (cycleDirichlet_nonneg wt hwt f g))
  have hyE : cycleDirichlet (inc := BagEdge.Incident) wt f g ≤ E :=
    le_add_of_nonneg_left (add_nonneg (switchDirichlet_nonneg wt hwt f)
      (colorDirichlet_nonneg (fun e : BagEdge bags => e.val.val.1) wt hwt f))
  have hs := (safe_switch_elementary BagEdge.exists_incident wt hwt K hK f).trans
    (mul_le_mul_of_nonneg_left hsE (by positivity : 0 ≤ 60*N^2*K^2))
  have hc := (color_elementary (fun e : BagEdge bags => e.val.val.1) wt hwt K hK
    (color_clamp_comparability hbags height hheight hstep D hD w hw lo hi hlo) f).trans
    (mul_le_mul_of_nonneg_left hcE (by positivity : 0 ≤ 12*N*K))
  have hy := (cycle_elementary BagEdge.exists_incident wt hwt f g).trans
    (mul_le_mul_of_nonneg_left hyE (by positivity : 0 ≤ 6*N))
  have hl := total_cell_demand_load (hbags := hbags) (hG := hG) height hheight hstep D hD w hw lo hi hlo hlohi M f g
  change (∑ d : Demand hbags hG, gibbs wt d.1.1 * gibbs wt d.1.2 * d.cellCost f) ≤
    K^4*T*((∑ A : PM BagEdge.Incident, gibbs wt A *
      ∑ B ∈ safeDestinations wt K A, (f A.val-f B.val)^2) + 4*
      ∑ A : PM BagEdge.Incident, ∑ B : PM BagEdge.Incident, gibbs wt A*gibbs wt B*
      ∑ S ∈ components (inc := BagEdge.Incident) (A.val∪B.val), cycleSquare f g A.val B.val S) at hl
  have hload := hl.trans (mul_le_mul_of_nonneg_left (add_le_add hs (mul_le_mul_of_nonneg_left hy (by norm_num)))
    (by dsimp [T]; positivity : 0 ≤ K^4*T))
  have hv := variance_cell_demand_bound (hbags := hbags) (hG := hG) wt hwt M f
  have hvar := hv.trans (add_le_add (mul_le_mul_of_nonneg_left hload (by positivity : 0 ≤ 3*N^3))
    (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ N^2)))
  have hraw : MatchingFPRAS.FiniteVariance.variance (gibbs (inc := BagEdge.Incident) wt) (fun A => f A.val) ≤
      (180*N^5*K^6*T+72*N^4*K^4*T+12*N^3*K)*E := by
    rw [MatchingFPRAS.FiniteVariance.variance_eq_pair _ _ (gibbs_sum wt hwt M)]
    calc
      _ ≤ _ := hvar
      _ = _ := by ring
  have htag : T ≤ (10*N)^30 := by
    have h := tag_card_bound (V := V) (E := BagEdge bags) (Fintype.card V) hN le_rfl (bag_edges_card_le hbags hG)
    dsimp only [T,N]
    exact_mod_cast h
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ Fintype.card V by omega)
  have hcoef := MatchingFPRAS.energy_coefficient_bound hN1 hD hT0 htag
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hE)

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬(ends e).IsDiag)

include hloop

omit [Fintype E] [DecidableEq E] in
lemma PM.twice_card (A : PM (fun e v => v ∈ ends e)) : 2*A.val.card = Fintype.card V := by
  classical
  have hv (v : V) : (∑ e ∈ A.val, if v ∈ ends e then (1:ℕ) else 0) = 1 := by
    obtain ⟨e,⟨he,hev⟩,hu⟩ := A.property.2 v (Finset.mem_univ v)
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro f hf hfe
      have : v ∉ ends f := fun hfv => hfe (hu f ⟨hf,hfv⟩)
      simp [this]
    · exact fun h => (h he).elim
  have he (e : E) : (∑ v : V, if v ∈ ends e then (1:ℕ) else 0) = 2 := by
    have hs : Finset.univ.filter (fun v => v ∈ ends e) = (ends e).toFinset := by
      ext v; simp
    rw [← Finset.sum_filter,Finset.sum_const,smul_eq_mul,mul_one,hs]
    exact Sym2.card_toFinset_of_not_isDiag _ (hloop e)
  calc
    _ = ∑ e ∈ A.val, ∑ v : V, if v ∈ ends e then (1:ℕ) else 0 := by
      simp [he,Nat.mul_comm]
    _ = ∑ v : V, ∑ e ∈ A.val, if v ∈ ends e then (1:ℕ) else 0 := by rw [Finset.sum_comm]
    _ = _ := by simp [hv]

omit [Fintype E] [DecidableEq E] in
lemma PM.card_eq (A B : PM (fun e v => v ∈ ends e)) : A.val.card = B.val.card := by
  have ha := A.twice_card ends hloop
  have hb := B.twice_card ends hloop
  omega

omit hloop

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma matchingWeight_compare {w z : E → ℝ} (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (_hc : 0 ≤ c) (h : ∀ e, w e ≤ c*z e)
    (A : PM (fun e v => v ∈ ends e)) :
    matchingWeight w A ≤ c^A.val.card*matchingWeight z A := by
  calc
    _ ≤ ∏ e ∈ A.val, c*z e := Finset.prod_le_prod₀ (fun edge _ => hw edge) (fun edge _ => h edge)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const]; rfl

include hloop

omit [DecidableEq E] in
lemma partition_compare {w z : E → ℝ} (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ e, w e ≤ c*z e)
    (A : PM (fun e v => v ∈ ends e)) :
    partition (inc := fun e v => v ∈ ends e) w ≤
      c^A.val.card*partition (inc := fun e v => v ∈ ends e) z := by
  classical
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro B _
  have hh := matchingWeight_compare ends hw c hc h B
  rwa [PM.card_eq ends hloop B A] at hh

omit [DecidableEq E] in
lemma gibbs_compare {w z : E → ℝ} (hw : ∀ e, 0 < w e) (hz : ∀ e, 0 < z e)
    (c : ℝ) (hc : 0 ≤ c) (hwz : ∀ e, w e ≤ c*z e) (hzw : ∀ e, z e ≤ c*w e)
    (A : PM (fun e v => v ∈ ends e)) :
    gibbs w A ≤ c^(Fintype.card V)*gibbs z A := by
  have hwa := matchingWeight_compare ends (fun e => (hw e).le) c hc hwz A
  have hpz := partition_compare ends hloop (fun e => (hz e).le) c hc hzw A
  have hprod := mul_le_mul hwa hpz (le_of_lt (partition_pos z hz A))
    (mul_nonneg (pow_nonneg hc _) (matchingWeight_pos z hz A).le)
  have he : c^A.val.card*c^A.val.card = c^(Fintype.card V) := by
    rw [← pow_add,← A.twice_card ends hloop]
    congr 1; omega
  have hh : matchingWeight w A*partition (inc := fun e v => v ∈ ends e) z ≤
      c^(Fintype.card V)*matchingWeight z A*partition (inc := fun e v => v ∈ ends e) w := by
    calc
      _ ≤ (c^A.val.card*matchingWeight z A)*(c^A.val.card*partition (inc := fun e v => v ∈ ends e) w) := hprod
      _ = _ := by rw [← he]; ring
  unfold gibbs
  rw [← mul_div_assoc,div_le_div_iff₀ (partition_pos w hw A) (partition_pos z hz A)]
  exact hh

end MatchingFPRAS.Transport

end OAI
