import OAI.MathematicalPhysics.Heisenberg.PinDensity

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

end
end
end
end
end
end
end
end
end

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Pin
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def unpinned (E : Set V) : Finset V := Finset.univ.filter (fun j=>j∉E)

theorem finite_pin_induction (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω,0 ≤ μ ω) (hpos : 0 < ∑ ω,μ ω) (hs : Stable (lawSymbol μ π))
    (E₀ : Set V) (admissible : Finset V → Prop) (p : ℝ) (_hp : 0 ≤ p)
    (hstep : ∀ E : Set V,E₀ ⊆ E → ∀ T : Finset V,T.Nonempty →
      admissible T → Disjoint E (T : Set V) →
      (∀ U : Finset V,admissible U → Disjoint (E∪(T:Set V)) (U:Set V) →
        (∑ ω,if ∀ i∈U,¬HasHit (π ω) (E∪(T:Set V)) i then
          pinDensity μ π (E∪(T:Set V)) ω else 0) ≤ p^U.card) →
      2*returnFraction μ π E T ≤ p) :
    ∀ E : Set V,E₀ ⊆ E → ∀ T : Finset V,admissible T → Disjoint E (T:Set V) →
      (∑ ω,if ∀ i∈T,¬HasHit (π ω) E i then pinDensity μ π E ω else 0) ≤ p^T.card := by
  classical
  let Good := fun E : Set V=>∀ T : Finset V,admissible T → Disjoint E (T:Set V) →
    (∑ ω,if ∀ i∈T,¬HasHit (π ω) E i then pinDensity μ π E ω else 0) ≤ p^T.card
  suffices h : ∀ n : ℕ,∀ E : Set V,(unpinned E).card=n → E₀⊆E → Good E by
    intro E hE
    exact h _ E rfl hE
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hcard hE T hT hET
    by_cases hn : T.Nonempty
    · have hproper : unpinned (E∪(T:Set V)) ⊂ unpinned E := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro i hi
          have hh : i∉E ∧ i∉T := by simpa [unpinned] using hi
          simpa [unpinned] using hh.1
        · intro heq
          obtain ⟨j,hj⟩:=hn
          have hjE : j∉E := fun h=>Set.disjoint_left.mp hET h hj
          have hh : j∈unpinned (E∪(T:Set V)) := by rw [heq]; simpa [unpinned] using hjE
          have hh' : j∉T := (by simpa [unpinned] using hh : j∉E ∧ j∉T).2
          exact hh' hj
      have hlt : (unpinned (E∪(T:Set V))).card < n := by
        rw [←hcard]
        exact Finset.card_lt_card hproper
      have hgood : Good (E∪(T:Set V)) := ih _ hlt _ rfl
        (fun i hi=>Or.inl (hE hi))
      have hr:=hstep E hE T hn hT hET hgood
      have htest:=finite_simultaneous_pin_test μ π hμ hpos hs E T hn hET
      apply htest.trans
      apply pow_le_pow_left₀ _ hr
      apply mul_nonneg (by norm_num)
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro ω _
      split_ifs
      · exact pinDensity_nonneg μ π hμ hpos _ _
      · exact le_refl 0
    · have ht : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst T
      simpa using (pinDensity_sum μ π hμ hpos E).le

end Heisenberg.Pin

end

noncomputable section
open scoped BigOperators
namespace Heisenberg.Clocks

lemma factorial_lower_of_pos (R : ℕ) (hR : 1 ≤ R) :
    ((R:ℝ)/Real.exp 1)^R ≤ (R.factorial:ℝ) := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hs : (1:ℝ) ≤ Real.sqrt (2*Real.pi*R) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [Real.pi_gt_three]
  calc
    _ ≤ Real.sqrt (2*Real.pi*R)*((R:ℝ)/Real.exp 1)^R :=
      le_mul_of_one_le_left (by positivity) hs
    _ ≤ _ := Stirling.le_factorial_stirling R

lemma geometric_le_recip (R : ℕ) : (1/2:ℝ)^R ≤ 1/(1+(R:ℝ)) := by
  have h : (1:ℝ)+R ≤ 2^R := by
    have := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 1) R
    norm_num at this ⊢
    linarith
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) h

theorem binomial_clock_tail (n R : ℕ) (B δ s : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hR : 1 ≤ R)
    (hsmall : ((n+2+R:ℕ):ℝ)*δ ≤ 2*s)
    (hlarge : 8*B*Real.exp 1*s ≤ R) :
    ((n+2+R).choose R:ℝ)*(2*B*δ)^R ≤ 1/(1+(R:ℝ)) := by
  have hfact : 0 < (R.factorial:ℝ) := by positivity
  have hr : 0 < (R:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hR)
  calc
    _ ≤ (((n+2+R:ℕ):ℝ)^R/(R.factorial:ℝ))*(2*B*δ)^R :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div R (n+2+R)) (by positivity)
    _ = (((n+2+R:ℕ):ℝ)*(2*B*δ))^R/(R.factorial:ℝ) := by rw [mul_pow]; ring
    _ ≤ (4*B*s)^R/(R.factorial:ℝ) := by
      apply div_le_div_of_nonneg_right _ hfact.le
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    _ ≤ (4*B*s)^R/(((R:ℝ)/Real.exp 1)^R) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_lower_of_pos R hR)
    _ = (4*B*s/((R:ℝ)/Real.exp 1))^R := (div_pow ..).symm
    _ ≤ (1/2:ℝ)^R := by
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_iff₀ (by positivity : 0 < (R:ℝ)/Real.exp 1)).mpr
      rw [←mul_div_assoc]
      apply (le_div_iff₀ (Real.exp_pos 1)).mpr
      nlinarith
    _ ≤ _ := geometric_le_recip R

end Heisenberg.Clocks

end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
open Matrix
namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Schedule Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma exposedStep_cutFactors (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (P : Set (Fin (n+1)×V)) (I : Set V) (base : Fin (n+1) → Bool) (i : Fin (n+1)) :
    cutFactors n a b p P (fun c t=>holeCut (finRotate (n+1)) (fun j=>Equiv.swap (a j) (b j)) c P t∩I) base i=
      exposedStep (finRotate (n+1)) a b base P I p i := rfl

theorem period_return_two_ends (n q : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V)) (I : Set V)
    (hP : ∀ z,z.2∉I → z∈P) (t : Fin (n+1)) (T : Finset P) (J : Finset V)
    (himage : T.image Subtype.val=targetsAt n t J) (hJ : ∀ j∈J,j∈I)
    (u v : ℕ) (huv : u+v ≤ n+1) (rF rB : ℝ)
    (hF : ∀ f : ((Fin (n+1) → Bool) → EuclideanSpace ℝ V),
      (∀ c j,0 ≤ (f c).ofLp j ∧ (f c).ofLp j ≤ 1) →
      (∀ c j,j∈J → (f c).ofLp j=1) →
      (∀ c j,j∉holeCut (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c P t∩I → (f c).ofLp j=0) →
      rF ≤ ∑ c,layerMass (finRotate (n+1)) a b P p c *
        (‖f c‖^2-‖exposedSweep (finRotate (n+1)) a b c P I p (run t) u (f c)‖^2))
    (hB : ∀ f : ((Fin (n+1) → Bool) → EuclideanSpace ℝ V),
      (∀ c j,0 ≤ (f c).ofLp j ∧ (f c).ofLp j ≤ 1) →
      (∀ c j,j∈J → (f c).ofLp j=1) →
      (∀ c j,j∉holeCut (finRotate (n+1)).symm
        (fun i=>Equiv.swap (a ((finRotate (n+1)).symm i)) (b ((finRotate (n+1)).symm i))) c P t∩I → (f c).ofLp j=0) →
      rB ≤ ∑ c,layerMass (finRotate (n+1)).symm (a ∘ (finRotate (n+1)).symm)
        (b ∘ (finRotate (n+1)).symm) P (p ∘ (finRotate (n+1)).symm) c *
        (‖f c‖^2-‖exposedSweep (finRotate (n+1)).symm (a ∘ (finRotate (n+1)).symm)
          (b ∘ (finRotate (n+1)).symm) c P I (p ∘ (finRotate (n+1)).symm)
          (fun j=>reverseIndex q (run (reverseIndex q t) j)) v (f c)‖^2)) :
    (∑ c,layerMass (finRotate (n+1)) a b P p c *
      returnCount (layerHistory (finRotate (n+1)) (fun i=>Equiv.swap (a i) (b i)) c) P T) ≤
        (J.card:ℝ)-(rF+rB)/2 := by
  let s:=finRotate (n+1)
  let D:=fun c i=>holeCut s (fun j=>Equiv.swap (a j) (b j)) c P i∩I
  have hT : ∀ base j,j∈T → j.val.2∈D base j.val.1 := by
    intro c j hj
    have ht : j.val∈targetsAt n t J := himage ▸ Finset.mem_image.mpr ⟨j,hj,rfl⟩
    have hh:=(mem_targetsAt ..).mp ht
    refine ⟨?_,hJ _ hh.2⟩
    exact fun h=>Set.disjoint_left.mp (missing_disjoint_pins _ P) h j.property
  have hQ : ∀ base,(MissingSet (layerHistory s (fun i=>Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆
      {z | z.2∈D base z.1} := by
    intro c z hz
    exact ⟨hz.1,by by_contra h; exact hz.2 (hP z h)⟩
  obtain ⟨A,hA,hAJ,hAs,hret⟩:=cut_return_energy_at n a b p hp P D t T J himage hT hQ
  let f:=fun c=>WithLp.toLp 2 (A c)
  have hf : ∀ c j,0 ≤ (f c).ofLp j ∧ (f c).ofLp j ≤ 1 := hA
  have hfJ : ∀ c j,j∈J → (f c).ofLp j=1 := hAJ
  have hfs : ∀ c j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) c P t∩I → (f c).ofLp j=0 := hAs
  have hF' := hF f hf hfJ hfs
  have hB' := hB (fun c=>f (c ∘ s)) (fun c j=>hf _ _) (fun c j hj=>hfJ _ _ hj) (by
    intro c j hj
    apply hfs
    have he := holeCut_reverse s a b (c ∘ s) P t
    have hc : (c ∘ s) ∘ s.symm=c := by funext i; simp
    rw [hc] at he
    exact fun h=>hj (by rw [he]; exact h))
  have hbmean : (∑ c,layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) c *
      (‖f (c ∘ s)‖^2-‖exposedSweep s.symm (a ∘ s.symm) (b ∘ s.symm) c P I (p ∘ s.symm)
        (fun j=>reverseIndex q (run (reverseIndex q t) j)) v (f (c ∘ s))‖^2))=
      ∑ c,layerMass s a b P p c *
      (‖f c‖^2-‖euclideanMap (prefixMatrix
        (fun j=>(exposedStep s a b c P I p (run t (n+1-1-j))).transpose) v) (f c)‖^2) := by
    let e : ((Fin (n+1) → Bool)) ≃ ((Fin (n+1) → Bool)) := Equiv.arrowCongr s (Equiv.refl Bool)
    conv_lhs => rw [←e.sum_comp]
    apply Finset.sum_congr rfl
    intro c _
    change layerMass s.symm (a ∘ s.symm) (b ∘ s.symm) P (p ∘ s.symm) (c ∘ s.symm) *
      (‖f ((c ∘ s.symm) ∘ s)‖^2-‖exposedSweep s.symm (a ∘ s.symm) (b ∘ s.symm) (c ∘ s.symm) P I (p ∘ s.symm)
        (fun j=>reverseIndex q (run (reverseIndex q t) j)) v (f ((c ∘ s.symm) ∘ s))‖^2)=_
    have hc : (c ∘ s.symm) ∘ s=c := by funext i; simp
    rw [hc,layerMass_reverse,reversed_period_sweep q a b P p c I t v (by omega)]
  rw [hbmean] at hB'
  have he : (rF+rB)/2 ≤ ∑ c,layerMass s a b P p c *
      energy (product (n+1) (fun i=>cutFactors n a b p P D c (run t i))) (A c) := by
    have hh : rF+rB ≤ (∑ c,layerMass s a b P p c *
      (‖f c‖^2-‖exposedSweep s a b c P I p (run t) u (f c)‖^2))+
      (∑ c,layerMass s a b P p c *(‖f c‖^2-‖euclideanMap (prefixMatrix
        (fun j=>(exposedStep s a b c P I p (run t (n+1-1-j))).transpose) v) (f c)‖^2)) := add_le_add hF' hB'
    apply (div_le_div_of_nonneg_right hh (by norm_num)).trans
    rw [←Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_le_sum
    intro c _
    rw [←mul_add,mul_div_assoc,exposedSweep_prefix]
    have hK : ∀ j,j < n+1 → Heisenberg.MatrixContraction.DoublySubstochastic (exposedStep s a b c P I p (run t j)) := by
      intro j _
      exact exposedStep_substochastic s a b c P I p hp _
    have ht:=energy_two_prefixes (fun j=>exposedStep s a b c P I p (run t j)) (n+1) u v huv hK (f c)
    apply mul_le_mul_of_nonneg_left _ (layerMass_nonneg s a b P p hp c)
    rw [prefix_product (fun j=>exposedStep s a b c P I p (run t j)) (n+1)] at ht
    exact ht
  linarith

end Heisenberg.Exposure

end
end

end OAI
