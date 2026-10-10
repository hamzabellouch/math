import OAI.Geometry.PinnedDistances.IncomingFibers

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}

lemma PreparedGraph.edgeCount_pos (h : PreparedGraph V I G θ γ c η) (hη : η<θ) : 0<G.edgeCount := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hp : 0<(θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) :=
    mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)
  exact hp.trans_le h.lower

lemma PreparedGraph.edge_domination (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (x y : V) :
    G.edgeLaw x y ≤ (1/(θ-η))*pairProb Finset.univ x y := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hden : 0<(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) := mul_pos (by linarith) (by linarith)
  by_cases hxy : x=y
  · subst y; simp [G.edgeLaw_diag,pairProb]
  · have he : pairProb Finset.univ x y=1/((Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by simp [pairProb,hxy]
    rw [he]
    unfold Core.Fibers.edgeLaw
    split_ifs
    · have hh := one_div_le_one_div_of_le (mul_pos (sub_pos.mpr hη) hden) (by simpa only [mul_assoc] using h.lower)
      calc
        1 / G.edgeCount ≤ 1 / ((θ-η)*((Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1))) := hh
        _ = _ := by rw [one_div_mul_one_div]
    · positivity

lemma PreparedGraph.degree_law (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η) (x : V) :
    2*((θ-η)/(θ+η/8))*prob Finset.univ x ≤ (∑ y, G.edgeLaw x y)+(∑ y, G.edgeLaw y x) := by
  rw [G.degree_marginal]
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hn0 : (0:ℝ)<Fintype.card V := by linarith
  have hnm : 0<(Fintype.card V : ℝ)-1 := by linarith
  have hθ : 0<θ+η/8 := by linarith
  have hd := h.degree x
  have hu := h.upper
  have hh : (2*(θ-η)*((Fintype.card V : ℝ)-1))/((θ+η/8)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) ≤
      G.degree (-1) Finset.univ x/G.edgeCount := by
    apply div_le_div₀ _ hd (h.edgeCount_pos hη) hu
    exact (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hη.le)) hnm.le).trans hd
  have he : (2*(θ-η)*((Fintype.card V : ℝ)-1))/((θ+η/8)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) =
      2*((θ-η)/(θ+η/8))*prob Finset.univ x := by
    simp only [prob,Finset.mem_univ,ite_true,Finset.card_univ]
    field_simp
  rwa [he] at hh

lemma PreparedGraph.heavy_bound (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η) (D : Finset V) :
    G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      ((θ+η)/(θ-η))*pairCell Finset.univ D := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hden : 0<(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) := mul_pos (by linarith) (by linarith)
  have hD : 0 ≤ (D.card : ℝ)*((D.card : ℝ)-1) := by
    by_cases hz : D.card=0
    · simp [hz]
    · have hh : (1:ℝ)≤D.card := by exact_mod_cast (show 1≤D.card by omega)
      positivity
  have hb := h.subset D
  have hcmp : G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      ((θ+η)*(D.card : ℝ)*((D.card : ℝ)-1))/((θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by
    apply div_le_div₀ _ hb (mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)) h.lower
    simpa only [mul_assoc] using mul_nonneg (show 0≤θ+η by linarith) hD
  convert hcmp using 1
  rw [pairCell_formula]
  simp only [Finset.univ_inter,Finset.card_univ]
  field_simp

lemma PreparedGraph.small_heavy_bound (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η)
    (D : Finset V) (hDsz : (D.card : ℝ)≤(Fintype.card V : ℝ)^(1-c)) :
    G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      (η/(θ-η))*pairCell Finset.univ D := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hD : 0 ≤ (D.card : ℝ)*((D.card : ℝ)-1) := by
    by_cases hz : D.card=0
    · simp [hz]
    · have hh : (1:ℝ)≤D.card := by exact_mod_cast (show 1≤D.card by omega)
      positivity
  have hcmp : G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D / G.edgeCount ≤
      (η*(D.card : ℝ)*((D.card : ℝ)-1))/((θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by
    apply div_le_div₀ _ (h.small D hDsz) (mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)) h.lower
    simpa only [mul_assoc] using mul_nonneg hη0 hD
  convert hcmp using 1
  rw [pairCell_formula]
  simp only [Finset.univ_inter,Finset.card_univ]
  field_simp

end WeakPinned

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance SmallFiber
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def qCell (C : Finset V) : ℝ := ∑ x ∈ C, ∑ y ∈ C, G.edgeLaw x y

lemma qCell_eq (C : Finset V) : G.qCell C = SmallFiber.edgeCell G.fiberWeight (fun e => prob (G.targets e)) G.source C := by
  unfold qCell SmallFiber.edgeCell SmallFiber.edgeLaw
  simp_rw [G.sampling_fiber]

omit [Fintype V] in
omit [Fintype I] in
lemma fiber_mass (e : I) (C : Finset V) : mass (prob (G.targets e)) C=(G.size C e : ℝ)/(G.targets e).card := by
  rw [mass,sum_prob_cell]
  rfl

lemma qCell_split (hne : ∀ e, (G.targets e).Nonempty) (lam : ℝ) (C : Finset V) :
    G.qCell C = slice G.fiberWeight (fun e => prob (G.targets e)) G.source lam C + G.heavyCount lam C/G.edgeCount := by
  classical
  rw [G.qCell_eq,edgeCell_formula]
  unfold slice heavyCount
  simp only [Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hk : (0:ℝ)<(G.targets e).card := by exact_mod_cast Finset.card_pos.mpr (hne e)
  have hm := G.fiber_mass e C
  have hprod : G.fiberWeight e*mass (prob (G.targets e)) C=(G.size C e : ℝ)/G.edgeCount := by
    rw [hm,fiberWeight]
    field_simp
  have hcmp : lam*((G.targets e).card : ℝ) ≤ (G.size C e : ℝ) ↔ lam ≤ mass (prob (G.targets e)) C := by
    rw [hm,le_div_iff₀ hk]
  simp only [hcmp]
  by_cases hx : G.source e ∈ C <;> by_cases hp : mass (prob (G.targets e)) C<lam
  · simp [hx,hp,not_le.mpr hp]
  · simp [hx,hp,le_of_not_gt hp,hprod]
  · simp [hx]
  · simp [hx]

omit [Fintype I] in
lemma qCell_bound {B : ℝ} (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y) (C : Finset V) :
    G.qCell C ≤ B*pairCell Finset.univ C := by
  unfold qCell pairCell
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hdom x y))

end WeakPinned.Core.Fibers

namespace WeakPinned.Variance
open scoped BigOperators
variable {V : Type u5} [Fintype V] [DecidableEq V]

lemma weighted_pair (m : Finset V → ℝ) (q : V → V → ℝ) :
    weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, q x y)=
      ∑ x, ∑ y, q x y*weightedOverlap m x y := by
  have hc (C : Finset V) : (∑ x ∈ C, ∑ y ∈ C, q x y)=
      ∑ x, ∑ y, q x y*(if x∈C ∧ y∈C then (1:ℝ) else 0) := by
    simp only [mul_ite,mul_one,mul_zero,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  simp only [weightedIntegral,hc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [weightedOverlap,weightedIntegral,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  ring

lemma weighted_additive (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (q : V → V → ℝ) (hdiag : ∀ x, q x x=0) (h1 : (∑ x, ∑ y, q x y)=1) :
    weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, q x y)=
      b+∑ x, ((∑ y, q x y)+(∑ y, q y x))*S x := by
  rw [weighted_pair]
  have hp (x y : V) : q x y*weightedOverlap m x y=q x y*(b+S x+S y) := by
    by_cases hxy : x=y
    · subst y; simp [hdiag]
    · rw [hL x y hxy]
  simp_rw [hp,mul_add,Finset.sum_add_distrib]
  have hb : (∑ x, ∑ y, q x y*b)=b := by
    simp only [← Finset.sum_mul,h1,one_mul]
  rw [hb]
  simp only [← Finset.sum_mul,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun x y => q x y*S y)]
  simp only [← Finset.sum_mul]
  ring

lemma uniform_additive (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) (hn : 2≤Fintype.card V) :
    weightedIntegral m (pairCell Finset.univ)=b+2*(∑ x, prob Finset.univ x*S x) := by
  have hsum : (∑ x : V, ∑ y : V, pairProb Finset.univ x y)=1 := by
    simp_rw [sum_pairProb Finset.univ (by simpa using hn)]
    exact sum_prob Finset.univ (Finset.card_pos.mp (by simpa using (show 0<Fintype.card V by omega)))
  have hh := weighted_additive m b S hL (pairProb Finset.univ) (by intro x; simp [pairProb]) hsum
  change weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, pairProb Finset.univ x y) = _
  rw [hh]
  simp_rw [pairProb_symm Finset.univ _ _,sum_pairProb Finset.univ (by simpa using hn)]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

end WeakPinned.Variance

namespace WeakPinned
open scoped BigOperators
open Variance SmallFiber
variable {V : Type u6} {I : Type u7} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}

lemma PreparedGraph.overlap_lower (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η)
    (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ) (hS : ∀ x, 0≤S x)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) :
    weightedIntegral m (pairCell Finset.univ) -
      (2-2*((θ-η)/(θ+η/8)))*(∑ x, prob Finset.univ x*S x) ≤ weightedIntegral m G.qCell := by
  change _ ≤ weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, G.edgeLaw x y)
  rw [weighted_additive m b S hL G.edgeLaw G.edgeLaw_diag (G.sum_edgeLaw (h.edgeCount_pos hη)),
    uniform_additive m b S hL h.card_ge]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_right (h.degree_law hη hη0 x) (hS x))
  have he : (∑ x : V, 2*((θ-η)/(θ+η/8))*prob Finset.univ x*S x)=
      (2*((θ-η)/(θ+η/8)))*(∑ x : V, prob Finset.univ x*S x) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he] at hh
  linarith

/-- A fully quantitative version of small-overlap before either scale branch.
The slice is the actual original fiber mass, not an assumed error term. -/
lemma PreparedGraph.small_overlap (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (hη0 : 0≤η)
    (m : Finset V → ℝ) (hm : ∀ C, 0 ≤ m C) (b : ℝ) (S : V → ℝ) (hS : ∀ x, 0≤S x)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) :
    (θ/(θ-η))*weightedIntegral m (fun C => if (C.card : ℝ)≤(Fintype.card V : ℝ)^(1-c)
      then pairCell Finset.univ C else 0) ≤
      weightedIntegral m (slice G.fiberWeight (fun e => prob (G.targets e)) G.source (1/Real.log (Fintype.card V : ℝ))) +
      ((θ+η)/(θ-η)-1)*weightedIntegral m (pairCell Finset.univ) +
      (2-2*((θ-η)/(θ+η/8)))*(∑ x, prob Finset.univ x*S x) := by
  have hlo := h.overlap_lower hη hη0 m b S hS hL
  have hne : ∀ e, (G.targets e).Nonempty := by
    intro e
    have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by have := h.card_ge; omega)
    exact Finset.card_pos.mp (by exact_mod_cast ((Real.rpow_pos_of_pos hn γ).trans (h.fiber e)))
  have hpoint (C : Finset V) : G.qCell C ≤
      slice G.fiberWeight (fun e => prob (G.targets e)) G.source (1/Real.log (Fintype.card V : ℝ)) C +
      ((θ+η)/(θ-η))*pairCell Finset.univ C -
      (θ/(θ-η))*(if (C.card : ℝ)≤(Fintype.card V : ℝ)^(1-c) then pairCell Finset.univ C else 0) := by
    rw [G.qCell_split hne (1/Real.log (Fintype.card V : ℝ)) C]
    by_cases hC : (C.card : ℝ)≤(Fintype.card V : ℝ)^(1-c)
    · rw [ite_eq_left hC]
      have hh := h.small_heavy_bound hη hη0 C hC
      have he : (θ+η)/(θ-η)-θ/(θ-η)=η/(θ-η) := by ring
      calc
        _ ≤ slice G.fiberWeight (fun e => prob (G.targets e)) G.source (1/Real.log (Fintype.card V : ℝ)) C + (η/(θ-η))*pairCell Finset.univ C := add_le_add_right hh _
        _ = _ := by rw [← he]; ring
    · simp only [ite_eq_right hC,mul_zero,sub_zero]
      exact add_le_add_right (h.heavy_bound hη hη0 C) _
  have hint := Finset.sum_le_sum (s:=Finset.univ) (fun C _ => mul_le_mul_of_nonneg_left (hpoint C) (hm C))
  change weightedIntegral m G.qCell ≤ _ at hint
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hint
  have hcomm (a : ℝ) (f : Finset V → ℝ) : (∑ C, m C*(a*f C))=a*weightedIntegral m f := by
    simp only [weightedIntegral,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _ => by ring)
  simp only [hcomm] at hint
  change weightedIntegral m G.qCell ≤ weightedIntegral m _+_ - _ at hint
  nlinarith

end WeakPinned

namespace WeakPinned
open scoped BigOperators
open Variance SmallFiber Global
variable {V : Type u8} {I : Type u9} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}
variable {K : Type u10} [Field K] [NumberField K]
variable (Z₁ Z₂ : V → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def overlapScale : ℝ := weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (pairCell Finset.univ)
def potentialScale : ℝ := ∑ x, prob Finset.univ x * totalPotential Z₁ Z₂ h₁ h₂ x

def smallOverlapScale (c : ℝ) : ℝ := weightedIntegral (totalMass Z₁ Z₂ h₁ h₂)
  (fun C => if (C.card : ℝ) ≤ (Fintype.card V : ℝ)^(1-c) then pairCell Finset.univ C else 0)

lemma overlapScale_nonneg : 0 ≤ overlapScale Z₁ Z₂ h₁ h₂ := by
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (totalMass_nonneg Z₁ Z₂ h₁ h₂ C) (pairCell_nonneg _ _))

lemma potentialScale_nonneg : 0 ≤ potentialScale Z₁ Z₂ h₁ h₂ := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (totalPotential_nonneg Z₁ Z₂ h₁ h₂ x)
  simp only [prob,Finset.mem_univ,ite_true]
  positivity

lemma smallOverlapScale_nonneg (c : ℝ) : 0 ≤ smallOverlapScale Z₁ Z₂ h₁ h₂ c := by
  apply Finset.sum_nonneg
  intro C _
  apply mul_nonneg (totalMass_nonneg Z₁ Z₂ h₁ h₂ C)
  dsimp only
  split_ifs
  · exact pairCell_nonneg _ _
  · exact le_refl _

lemma PreparedGraph.arithmetic_slice (h : PreparedGraph V I G θ γ c η) (hη : η < θ)
    (t : I → K) (ht : ∀ e y, y ∈ G.targets e → (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (τ lam H : ℝ) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card V:ℝ)) (hH : 0 ≤ H) :
    weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (slice G.fiberWeight (fun e => prob (G.targets e)) G.source lam) ≤
      (2*lam/τ^2+2*lam/(θ-η))*overlapScale Z₁ Z₂ h₁ h₂ +
      (2*τ/(θ-η))*potentialScale Z₁ Z₂ h₁ h₂ + 4*lam*H + 32*Real.exp (-H/2) := by
  have hne : ∀ e, (G.targets e).Nonempty := by
    intro e
    have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by have := h.card_ge; omega)
    exact Finset.card_pos.mp (by exact_mod_cast ((Real.rpow_pos_of_pos hn γ).trans (h.fiber e)))
  have hp : ∀ e y, 0 ≤ prob (G.targets e) y := by intro e y; unfold prob; split_ifs <;> positivity
  have hx : ∀ e, prob (G.targets e) (G.source e)=0 := by intro e; simp [prob,G.no_loop]
  have ht' : ∀ e y, prob (G.targets e) y ≠ 0 → (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e := by
    intro e y hy
    apply ht e y
    by_contra hn
    exact hy (by simp [prob,hn])
  have hdom : ∀ a b, a ≠ b → SmallFiber.edgeLaw G.fiberWeight (fun e => prob (G.targets e)) G.source a b ≤
      (1/(θ-η))/((Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)) := by
    intro a b hab
    have hh := h.edge_domination hη a b
    simpa [SmallFiber.edgeLaw,G.sampling_fiber,pairProb,hab, div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh := arithmetic_small_fiber Z₁ Z₂ h₁ h₂ h.card_ge G.fiberWeight (fun e => prob (G.targets e)) G.source t
    G.fiberWeight_nonneg (G.sum_fiberWeight (h.edgeCount_pos hη)) hp (fun e => sum_prob _ (hne e)) hx ht'
    (1/(θ-η)) τ lam H (by positivity) hlam hlam2 hτ hτ1 hτn hH hdom
  have he : (∑ x : V, totalPotential Z₁ Z₂ h₁ h₂ x)/(Fintype.card V:ℝ) = potentialScale Z₁ Z₂ h₁ h₂ := by
    simp only [potentialScale,prob,Finset.mem_univ,ite_true,Finset.card_univ,Finset.sum_div]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have ha : 2*(1/(θ-η))*τ/(Fintype.card V:ℝ)*(∑ x, totalPotential Z₁ Z₂ h₁ h₂ x) =
      (2*τ/(θ-η))*potentialScale Z₁ Z₂ h₁ h₂ := by rw [← he]; ring
  rw [ha] at hh
  convert hh using 1; unfold overlapScale; ring

/-- The genuine scale estimate, valid for every prepared arithmetic model.
All error terms are explicit and can be sent to zero uniformly in the field. -/
lemma PreparedGraph.arithmetic_small_overlap (h : PreparedGraph V I G θ γ c η) (hη : η < θ) (hη0 : 0 ≤ η)
    (t : I → K) (ht : ∀ e y, y ∈ G.targets e → (Z₁ (G.source e)-Z₁ y)*(Z₂ (G.source e)-Z₂ y)=t e)
    (τ H : ℝ) (hlam : 0 ≤ 1/Real.log (Fintype.card V:ℝ)) (hlam2 : 1/Real.log (Fintype.card V:ℝ) ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card V:ℝ)) (hH : 0 ≤ H) :
    smallOverlapScale Z₁ Z₂ h₁ h₂ c ≤
      (2*(1/Real.log (Fintype.card V:ℝ))/τ^2+2*(1/Real.log (Fintype.card V:ℝ))/(θ-η)+((θ+η)/(θ-η)-1))*overlapScale Z₁ Z₂ h₁ h₂ +
      (2*τ/(θ-η)+(2-2*((θ-η)/(θ+η/8))))*potentialScale Z₁ Z₂ h₁ h₂ +
      4*(1/Real.log (Fintype.card V:ℝ))*H + 32*Real.exp (-H/2) := by
  have hs := h.small_overlap hη hη0 (totalMass Z₁ Z₂ h₁ h₂) (totalMass_nonneg Z₁ Z₂ h₁ h₂)
    (baseConstant Z₁ Z₂ h₁ h₂) (totalPotential Z₁ Z₂ h₁ h₂) (totalPotential_nonneg Z₁ Z₂ h₁ h₂)
    (totalMass_overlap Z₁ Z₂ h₁ h₂ h.card_ge)
  have htS := h.arithmetic_slice Z₁ Z₂ h₁ h₂ hη t ht τ (1/Real.log (Fintype.card V:ℝ)) H hlam hlam2 hτ hτ1 hτn hH
  have hf : 1 ≤ θ/(θ-η) := (one_le_div (sub_pos.mpr hη)).mpr (by linarith)
  have he := mul_le_mul_of_nonneg_right hf (smallOverlapScale_nonneg Z₁ Z₂ h₁ h₂ c)
  change (θ/(θ-η))*smallOverlapScale Z₁ Z₂ h₁ h₂ c ≤ _ at hs
  change _ ≤ _ + ((θ+η)/(θ-η)-1)*overlapScale Z₁ Z₂ h₁ h₂ +
    (2-2*((θ-η)/(θ+η/8)))*potentialScale Z₁ Z₂ h₁ h₂ at hs
  nlinarith
end WeakPinned

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [DecidableEq P] [Fintype I]
lemma varianceCell_nonneg (w : I → ℝ) (B : I → Finset P) (T : ℝ)
    (hw : ∀ i, 0≤w i) (C : Finset P) : 0≤varianceCell w B T C := by
  unfold varianceCell
  split_ifs
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hw i)
    split_ifs <;> positivity

lemma reciprocal_card_sub_one {n k : ℝ} (hn : 2≤n) (hnk : n≤k) :
    1/(k-1) ≤ 2/n := by
  apply (div_le_div_iff₀ (by linarith : 0<k-1) (by linarith : 0<n)).mpr
  nlinarith

end WeakPinned.Variance

namespace WeakPinned
open scoped BigOperators Topology
open Filter Variance Global
variable {V : ℕ → Type u13} {I : ℕ → Type u14} {K : ℕ → Type u15} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

/-- Asymptotic arithmetic variance for arbitrary genuine uniform-subset
families. The domination and size assumptions are finite sampling data.
The exact arithmetic cancellation and small-overlap rate are already proved. -/
theorem arithmetic_variance_rate (w : ∀ j, I j → ℝ) (B : ∀ j, I j → Finset (V j))
    (γ c M₀ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ) (_hc1 : c<1) (hM : 0≤M₀)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hw : ∀ j i, 0≤w j i) (hW : ∀ j, (∑ i, w j i)≤1)
    (hsize : ∀ᶠ j in atTop, ∀ i, (Fintype.card (V j):ℝ)^γ ≤ ((B j i).card:ℝ))
    (hdom : ∀ᶠ j in atTop, ∀ x, (∑ i, w j i*prob (B j i) x)≤ M₀*prob Finset.univ x)
    (hsmall : Tendsto (fun j => smallOverlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0)) :
    Tendsto (fun j => weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
      (varianceCell (w j) (B j) ((Fintype.card (V j):ℝ)^(1-c))) /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) := by
  let n := fun j => (Fintype.card (V j):ℝ)
  let U := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A := fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let D := fun j => smallOverlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) c
  have hU (j) : 0≤U j := overlapScale_nonneg _ _ _ _
  have hA (j) : 0≤A j := potentialScale_nonneg _ _ _ _
  have hden (j) : 0<U j+A j+1 := by linarith [hU j,hA j]
  have hNγ : Tendsto (fun j => n j^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hcT : Tendsto (fun j => n j^(c-γ)) atTop (𝓝 0) :=
    by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0<γ-c)).comp hn
    convert h using 1; funext j; congr 1; ring
  have hlim : Tendsto (fun j => 4*(M₀+1)*n j^(c-γ)+4*M₀*(D j/(U j+A j+1))) atTop (𝓝 0) := by
    convert (hcT.const_mul (4*(M₀+1))).add (hsmall.const_mul (4*M₀)) using 1; simp
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun j => div_nonneg
      (Finset.sum_nonneg fun C _ => mul_nonneg (totalMass_nonneg _ _ _ _ C)
        (varianceCell_nonneg _ _ _ (hw j) C)) (hden j).le
  · filter_upwards [hn.eventually (eventually_ge_atTop (2:ℝ)),
      hNγ.eventually (eventually_ge_atTop (2:ℝ)), hsize,hdom] with j hjn hjγ hjs hjd
    have hnpos : 0<n j := by linarith
    have hnγpos : 0<n j^γ := Real.rpow_pos_of_pos hnpos _
    have hnP : 2≤Fintype.card (V j) := by exact_mod_cast hjn
    have hbs : ∀ i, 2≤(B j i).card := fun i => by exact_mod_cast (hjγ.trans (hjs i))
    have hbn : n j^γ ≤ n j := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤n j by linarith) hγ1.le
    have hk : ∀ i, 1/(((B j i).card:ℝ)-1)≤2/(n j^γ) := fun i => reciprocal_card_sub_one hjγ (hjs i)
    have hnerr : 1/(n j-1)≤2/(n j^γ) := reciprocal_card_sub_one hjγ hbn
    have hT : 1≤n j^(1-c) := Real.one_le_rpow (by linarith) (by linarith)
    have hτ : 0<n j^(-c) := Real.rpow_pos_of_pos hnpos _
    have hscale : n j^(-c)*n j≤n j^(1-c) := by
      calc
        _ = n j^(-c)*n j^(1:ℝ) := by rw [Real.rpow_one]
        _ = n j^((-c)+1) := (Real.rpow_add hnpos _ _).symm
        _ = n j^(1-c) := by congr 1;ring
        _ ≤ n j^(1-c) := le_rfl
    have hv := arithmetic_variance (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hnP (w j) (B j)
      (n j^(1-c)) M₀ (2/(n j^γ)) (n j^(-c)) (hw j) (hW j) hT hM
      (by positivity) hτ hscale hbs hk hnerr hjd
    have he : 2*(2/(n j^γ))*(M₀+1)/(n j^(-c))=4*(M₀+1)*n j^(c-γ) := by
      rw [Real.rpow_sub hnpos,Real.rpow_neg hnpos.le]
      field_simp
      ring
    rw [he] at hv
    change _≤4*(M₀+1)*n j^(c-γ)*U j+4*M₀*D j at hv
    have hratio : U j/(U j+A j+1)≤1 := (div_le_one (hden j)).mpr (by linarith [hA j])
    have hcoeff : 0≤4*(M₀+1)*n j^(c-γ) := by positivity
    calc
      _ ≤ (4*(M₀+1)*n j^(c-γ)*U j+4*M₀*D j)/(U j+A j+1) := div_le_div_of_nonneg_right hv (hden j).le
      _ = (4*(M₀+1)*n j^(c-γ))*(U j/(U j+A j+1))+4*M₀*(D j/(U j+A j+1)) := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hratio hcoeff]
end WeakPinned
noncomputable section
open Filter
open scoped Topology

end
end
end
end
end
end
end
end
end

end OAI
