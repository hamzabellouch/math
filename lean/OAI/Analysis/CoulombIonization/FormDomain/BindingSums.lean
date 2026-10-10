import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.ApproximateLipschitz
import OAI.Analysis.CoulombIonization.Variational.BindingNuclearSum
import OAI.Analysis.CoulombIonization.RadialBounds.BindingBounds

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CurrentBindingSums_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  bindingTotalMultiplier graphNuclear weightedMass weightedNuclear weightedPairs

def graphNuclearSum {N : ℕ} (F : fermionGraph N) : ℝ :=
  ∑ s,∑ i,∫ x, ‖graphComponent s none F x‖^2/‖x i‖

lemma graphNuclearSum_bound {N : ℕ} (F : fermionGraph N) :
    graphNuclearSum F ≤ ((N:ℝ)+1)*‖F‖^2 := by
  have hi (s : Spins N) (i : Fin N) :
      (∫ x, ‖graphComponent s none F x‖^2/‖x i‖) ≤
        (1/4:ℝ)*(∑ a, ‖graphComponent s (some (i,a)) F‖^2)+
          ‖graphComponent s none F‖^2 := by
    have hh := graphNuclear_bound (Z := 1) (by norm_num) F s i
    simpa only [one_mul,one_pow,graphNuclear_norm_sq,graphFormVector_value_eq] using hh
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => hi s i
  have hm := graphValue_norm_sq F
  have hg := fermionGraph_norm_sq F
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [← hm] at hs
  have hk : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  change graphNuclearSum F ≤ _ at hs
  nlinarith [mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hk,
    sq_nonneg ‖fermionGraphValue N F‖]

lemma binding_nuclear_sum_bound {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph N) :
    (∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i))) ≤
      (N:ℝ)*‖fermionGraphValue N F‖^2+ε*((N:ℝ)+1)*‖F‖^2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun s _ =>
      bindingWeight_nuclear_integral hR hε i (Lp.memLp (graphComponent s none F))
        (graph_nuclear_integrable F s i)
  have hn := mul_le_mul_of_nonneg_left (graphNuclearSum_bound F) hε.le
  have he : (∑ i : Fin N,∑ s : Spins N,
      ((∫ x, ‖graphComponent s none F x‖^2)+
        ε*(∫ x, ‖graphComponent s none F x‖^2/‖x i‖))) =
      (N:ℝ)*‖fermionGraphValue N F‖^2+ε*graphNuclearSum F := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,graph_mass_integral,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold graphNuclearSum
    rw [Finset.sum_comm]
  have hs' : (∑ i,weightedNuclear F i (fun x => bindingWeight R ε (x i))) ≤
      (N:ℝ)*‖fermionGraphValue N F‖^2+ε*graphNuclearSum F := by
    simpa only [weightedNuclear] using hs.trans_eq he
  exact hs'.trans (by nlinarith only [hn])

lemma sum_pair_tail_bound {N : ℕ} (P : Fin (N+1) → Fin (N+1) → ℝ)
    (W : Fin (N+1) → ℝ) (m c : ℝ)
    (hp : ∀ i j, i ≠ j → m ≤ (P i j+c*W i)+(P j i+c*W j)) :
    ((N:ℝ)+1)*(N:ℝ)*m ≤
      2*(∑ i,∑ j,if i ≠ j then P i j else 0)+2*(N:ℝ)*c*(∑ i,W i) := by
  classical
  let A (i j : Fin (N+1)) : ℝ := if i ≠ j then P i j+c*W i else 0
  let B (i j : Fin (N+1)) : ℝ := if i ≠ j then m else 0
  have hh : ∀ i j, B i j ≤ A i j+A j i := by
    intro i j
    by_cases hij : i ≠ j
    · simpa only [A,B,ite_eq_left hij,ite_eq_left hij.symm] using hp i j hij
    · obtain rfl := not_ne_iff.mp hij
      simp only [A,B,ne_eq,not_true_eq_false,ite_false,add_zero,le_refl]
  have hs := sum_pair_bound A B hh
  have hB : (∑ i,∑ j,B i j)=((N:ℝ)+1)*(N:ℝ)*m := by
    simp only [B,sum_excluding_const,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring
  have hA (i : Fin (N+1)) : (∑ j,A i j)=
      (∑ j,if i ≠ j then P i j else 0)+(N:ℝ)*c*W i := by
    calc
      _ = ∑ j,((if i ≠ j then P i j else 0)+(if i ≠ j then c*W i else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [A]
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_add_distrib,sum_excluding_const]; ring
  rw [hB] at hs
  simp only [hA,Finset.sum_add_distrib,← Finset.mul_sum] at hs
  linarith

lemma binding_pair_sum_bound {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : fermionGraph (N+1)) :
    ((N:ℝ)+1)*(N:ℝ)*‖fermionGraphValue (N+1) F‖^2 ≤
      2*(∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
        2*(N:ℝ)/R*weightedMass F (bindingTotalMultiplier hR hε).value := by
  classical
  let P (s : Spins (N+1)) (i j : Fin (N+1)) : ℝ :=
    ∫ x,bindingWeight R ε (x i)*(‖graphComponent s none F x‖^2/‖x i-x j‖)
  let W (s : Spins (N+1)) (i : Fin (N+1)) : ℝ :=
    ∫ x,bindingWeight R ε (x i)*‖graphComponent s none F x‖^2
  have hb (s : Spins (N+1)) := sum_pair_tail_bound (P s) (W s)
    (∫ x,‖graphComponent s none F x‖^2) R⁻¹
    (fun i j hij => bindingWeight_pair_integral hR hε i j hij (Lp.memLp _)
      (graph_pair_integrable F s i j hij))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ => hb s
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,graph_mass_integral] at hs
  have hP : (∑ s,∑ i,∑ j,if i ≠ j then P s i j else 0)=
      ∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)) := by
    unfold weightedPairs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [P]
    split_ifs <;> simp
  have hW : (∑ s,∑ i,W s i)=weightedMass F (bindingTotalMultiplier hR hε).value := by
    rw [bindingTotal_mass hR hε]
    unfold weightedMass
    exact Finset.sum_comm
  have ht := congrArg₂ (fun u v => 2*u+2*(N:ℝ)*R⁻¹*v) hP hW
  have he : 2*(∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
      2*(N:ℝ)*R⁻¹*weightedMass F (bindingTotalMultiplier hR hε).value =
      2*(∑ i,weightedPairs F i (fun x => bindingWeight R ε (x i)))+
        2*(N:ℝ)/R*weightedMass F (bindingTotalMultiplier hR hε).value := by ring
  exact hs.trans_eq (ht.trans he)

end Work_CurrentBindingSums_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma FermionMultiplier.mass_bound {N : ℕ} (p : FermionMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖^2 ≤ C^2*‖fermionGraphValue N F‖^2 := by
  rw [graphValue_norm_sq,graphValue_norm_sq,Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => l2_real_multiplier_bound _ _ p.value hC
    (p.apply_value F s)

lemma FermionMultiplier.kinetic_bound {N : ℕ} (p : FermionMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (D : Fin N × Fin 3 → ℝ)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D (i,a))
    (F : fermionGraph N) :
    (∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) (p.apply F)‖^2) ≤
      2*C^2*(∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2)+
        2*(∑ i,∑ a,D (i,a)^2)*‖fermionGraphValue N F‖^2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun a _ =>
      l2_two_multiplier_bound (graphComponent s (some (i,a)) F)
        (graphComponent s none F) (graphComponent s (some (i,a)) (p.apply F))
        p.value (fun x => lineDeriv ℝ p.value x (direction i a)) hC (hD i a)
        (p.apply_gradient F s i a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul] at hh
  rw [graphValue_norm_sq]
  convert hh using 1

theorem FermionMultiplier.graph_bound {N : ℕ} (p : FermionMultiplier N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : fermionGraph N, ‖p.apply F‖^2 ≤ C*‖F‖^2 := by
  classical
  obtain ⟨C,hC⟩ := p.bound
  choose D hD using p.gradient_bound
  let S : ℝ := ∑ i : Fin N,∑ a : Fin 3,D (i,a)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  refine ⟨3*C^2+2*S,by positivity,fun F => ?_⟩
  have hm := p.mass_bound hC F
  have hk := p.kinetic_bound hC D (fun i a x => hD (i,a) x) F
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  exact graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))

theorem quantum_approximate_multiplier {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    (p : FermionMultiplier N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2=1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪p.apply F,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ := by
  exact approximate_positive_form (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) p.apply (FermionMultiplier.graph_bound p)
    (fun F => ‖fermionGraphValue N F‖^2=1) (by positivity)
    (fun _ hη => quantum_sector_excess_near_minimizer hZ N hη) hδ

end CoulombAtom

end

end OAI
