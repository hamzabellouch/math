import OAI.Geometry.Kahler.BasePhaseFourier

namespace OAI

universe uKahler11043_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def phaseBand (ℓ : ℕ) : Finset ℤ := Finset.Icc (-(ℓ:ℤ)) ℓ
lemma mem_phaseBand (ℓ : ℕ) (n : ℤ) : n ∈ phaseBand ℓ ↔ |n| ≤ (ℓ:ℤ) := by simp [phaseBand,abs_le]

lemma phaseSum_extend {s t : Finset ℤ} (hst : s ⊆ t) (a : ℤ → ℂ) (z : Circle) :
    phaseSum s a z = phaseSum t (fun n => if n ∈ s then a n else 0) z := by
  classical
  unfold phaseSum
  calc
    _ = ∑ n ∈ s, (if n ∈ s then a n else 0)*phaseChar n z := by
      apply Finset.sum_congr rfl; intro n hn; simp [hn]
    _ = _ := Finset.sum_subset hst (fun n _ hn => by simp [hn])

lemma phaseBandwidth_band {W : Base → ℝ} {ℓ : ℕ} (hW : PhaseBandwidth W ℓ) (p : Sphere) :
    ∃ a : ℤ → ℂ, ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum (phaseBand ℓ) a z := by
  classical
  obtain ⟨s,a,hs,he⟩ := hW p
  refine ⟨fun n => if n ∈ s then a n else 0,?_⟩
  intro z
  rw [he]
  exact phaseSum_extend (fun n hn => (mem_phaseBand ℓ n).mpr (hs n hn)) a z

lemma phaseBandwidth_mono {W : Base → ℝ} {ℓ m : ℕ} (hW : PhaseBandwidth W ℓ) (hℓ : ℓ ≤ m) :
    PhaseBandwidth W m := by
  intro p
  obtain ⟨s,a,hs,he⟩ := hW p
  exact ⟨s,a,fun n hn => le_trans (hs n hn) (by exact_mod_cast hℓ),he⟩

lemma phaseBandwidth_add {W V : Base → ℝ} {ℓ : ℕ} (hW : PhaseBandwidth W ℓ) (hV : PhaseBandwidth V ℓ) :
    PhaseBandwidth (fun z => W z+V z) ℓ := by
  intro p
  obtain ⟨a,ha⟩ := phaseBandwidth_band hW p
  obtain ⟨b,hb⟩ := phaseBandwidth_band hV p
  refine ⟨phaseBand ℓ,fun n => a n+b n,fun n hn => (mem_phaseBand ℓ n).mp hn,?_⟩
  intro z
  simp only [Complex.ofReal_add,ha,hb,phaseSum,add_mul,Finset.sum_add_distrib]

lemma phaseBandwidth_zero (ℓ : ℕ) : PhaseBandwidth (fun _ => 0) ℓ := by
  intro p
  exact ⟨∅,fun _ => 0,by simp,by simp [phaseSum]⟩

lemma phaseBandwidth_sum {ι : Type uKahler11043_1} (s : Finset ι) (W : ι → Base → ℝ) {ℓ : ℕ}
    (hW : ∀ i ∈ s, PhaseBandwidth (W i) ℓ) : PhaseBandwidth (fun z => ∑ i ∈ s, W i z) ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phaseBandwidth_zero ℓ
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using phaseBandwidth_add (hW a (by simp))
      (ih (fun i hi => hW i (by simp [hi])))

lemma phaseChar_conj (n : ℤ) (z : Circle) : star (phaseChar n z)=phaseChar (-n) z := by
  unfold phaseChar
  rw [zpow_neg,Circle.coe_inv_eq_conj]
  rfl

lemma phaseSum_shift (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) (z : Circle) :
    (∑ n ∈ s, a n*phaseChar (k+n) z) =
      phaseSum (s.image (fun n => k+n)) (fun m => a (m-k)) z := by
  classical
  unfold phaseSum
  rw [Finset.sum_image (s := s) (g := fun n : ℤ => k+n) (fun n _ m _ he => add_left_cancel he)]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  omega

lemma phaseSum_negshift (s : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) (z : Circle) :
    (∑ n ∈ s, a n*phaseChar (-(k+n)) z) =
      phaseSum (s.image (fun n => -(k+n))) (fun m => a (-m-k)) z := by
  classical
  unfold phaseSum
  rw [Finset.sum_image (s := s) (g := fun n : ℤ => -(k+n)) (fun n _ m _ he => add_left_cancel (neg_injective he))]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  omega

lemma phaseSum_union {s t : Finset ℤ} (h : Disjoint s t) (a b : ℤ → ℂ) (z : Circle) :
    phaseSum s a z + phaseSum t b z = phaseSum (s ∪ t) (fun n => if n ∈ s then a n else b n) z := by
  classical
  unfold phaseSum
  rw [Finset.sum_union h]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    simp [hn]
  · apply Finset.sum_congr rfl
    intro n hn
    have hns : n ∉ s := fun hs => Finset.disjoint_left.mp h hs hn
    simp [hns]

lemma positive_shift_disjoint {s : Finset ℤ} {k ℓ : ℕ} (hℓ : ℓ < k) (hs : ∀ n ∈ s, |n| ≤ (ℓ:ℤ)) :
    Disjoint (s.image (fun n => (k:ℤ)+n)) (s.image (fun n => -((k:ℤ)+n))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro m hm hn
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hn
  have hs1 := (abs_le.mp (hs r hr)).1
  have hs2 := (abs_le.mp (hs t ht)).1
  omega

end PinchedHartogs.BaseConstruction

end

end OAI
