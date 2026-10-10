import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.OptimizerEnergy
import OAI.MathematicalPhysics.PEPSSubvolume.TensorDecomposition
import OAI.MathematicalPhysics.PEPSSubvolume.NeutralEnergy

namespace OAI

/-! Total crossing excitation bounds charged by physical boundaries. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.ContourEnergy
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.LocalTensorDecomposition
open PolynomialPEPS.Subvolume.OptimizerEnergy PolynomialPEPS.Subvolume.OptimizerNeutral
variable {L q : ℕ}

lemma commute_opposite_lifts (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    Commute (liftLocal X A) (liftLocal Xᶜ B) := by
  change liftLocal X A * liftLocal Xᶜ B = liftLocal Xᶜ B * liftLocal X A
  rw [← tensorAcross_one X A,← tensorAcross_one_left X B,← tensorAcross_mul,← tensorAcross_mul]
  simp

lemma commute_of_disjoint {S X : Finset (Vertex L)} (hSX : Disjoint S X)
    (H K : Operator L q) (hH : SupportedOn H S) (hK : SupportedOn K X) :
    Commute H K := by
  have hs : S ⊆ Xᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun hx => Finset.disjoint_left.mp hSX hv hx)
  obtain ⟨B,hB⟩ := SupportedOn.mono hs hH
  obtain ⟨A,hA⟩ := hK
  rw [hB,hA]
  exact (commute_opposite_lifts X A B).symm

lemma region_card_singleton (v : Vertex L) :
    Fintype.card (RegionConfiguration q {v}) = q := by
  simp [RegionConfiguration]

theorem edge_decomposition (hq : 0<q) (e : Edge L) (X : Finset (Vertex L))
    (v w : Vertex L) (hs : EdgeSites e={v,w}) (hv : v∈X) (hw : w∉X)
    (H : Operator L q) (hH : SupportedOn H (EdgeSites e)) :
    ∃ (A : (RegionConfiguration q {v} × RegionConfiguration q {v}) →
        Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
      (B : (RegionConfiguration q {v} × RegionConfiguration q {v}) →
        Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ),
      H=∑ i, tensorAcross X (A i) (B i) ∧
      (∑ i, ‖A i‖*‖B i‖) ≤ (q:ℝ)^2*opNorm H := by
  classical
  have hCS : {v} ⊆ EdgeSites e := by rw [hs]; simp
  have hCX : {v} ⊆ X := by simpa using hv
  have hT : EdgeSites e\{v} ⊆ Xᶜ := by
    intro z hz
    simp only [hs,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz.1 with h|h
    · exact False.elim (hz.2 h)
    · subst z; simpa using hw
  obtain ⟨A,B,he,hc⟩ := exists_local_tensor_decomposition hq (EdgeSites e) X {v} hCS hCX hT H hH
  refine ⟨A,B,he,?_⟩
  simpa only [region_card_singleton] using hc

end PolynomialPEPS.Subvolume.ContourEnergy

namespace PolynomialPEPS.Subvolume.ContourEnergy
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.LocalTensorDecomposition
open PolynomialPEPS.Subvolume.OptimizerEnergy PolynomialPEPS.Subvolume.OptimizerNeutral
variable {L q : ℕ}

def Splits (S X : Finset (Vertex L)) : Prop :=
  (∃ v∈S, v∈X) ∧ ∃ w∈S, w∉X

instance splitsDecidable (S X : Finset (Vertex L)) : Decidable (Splits S X) := by
  classical
  unfold Splits
  infer_instance

lemma not_splits (S X : Finset (Vertex L)) (h : ¬ Splits S X) :
    S ⊆ X ∨ Disjoint S X := by
  classical
  by_cases hs : S ⊆ X
  · exact Or.inl hs
  · right
    apply Finset.disjoint_left.mpr
    intro v hv hx
    apply h
    exact ⟨⟨v,hv,hx⟩,Finset.not_subset.mp hs⟩

lemma single_not_splits (v : Vertex L) (X : Finset (Vertex L)) : ¬Splits {v} X := by
  rintro ⟨⟨x,hx,hxi⟩,y,hy,hyi⟩
  simpa using hyi (by simpa only [Finset.mem_singleton.mp hx,Finset.mem_singleton.mp hy] using hxi)

lemma cross_inner_disjoint (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (S : Finset (Vertex L)) (n k : ℕ) (hk : k<n) (hcut : Splits S (X k))
    (hunique : ∀ j, j<n → Splits S (X j) → j=k)
    (j : ℕ) (hjk : j<k) : Disjoint S (X j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hx
  obtain ⟨w,hw,hwx⟩ := hcut.2
  have hjcut : Splits S (X j) := ⟨⟨v,hv,hx⟩,w,hw,fun hh => hwx (hX hjk.le hh)⟩
  have heq := hunique j (lt_trans hjk hk) hjcut
  omega

lemma cross_outer_subset (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (S : Finset (Vertex L)) (n k : ℕ) (_hk : k<n) (hcut : Splits S (X k))
    (hunique : ∀ j, j<n → Splits S (X j) → j=k)
    (j : ℕ) (hkj : k<j) (hj : j<n) : S ⊆ X j := by
  intro w hw
  by_contra hwx
  obtain ⟨v,hv,hvx⟩ := hcut.1
  have hjcut : Splits S (X j) := ⟨⟨v,hv,hX hkj.le hvx⟩,w,hw,hwx⟩
  have heq := hunique j hj hjcut
  omega

lemma neutral_cut_index (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (S : Finset (Vertex L)) (n : ℕ) (hn : ∀ j, j<n → ¬Splits S (X j)) :
    ∃ r≤n, (∀ j, j<r → Disjoint S (X j)) ∧
      ∀ j, r≤j → j<n → S ⊆ X j := by
  classical
  by_cases hex : ∃ k, k<n ∧ S ⊆ X k
  · let r := Nat.find hex
    have hr := Nat.find_spec hex
    refine ⟨r,hr.1.le,?_,?_⟩
    · intro j hj
      rcases not_splits S (X j) (hn j (lt_trans hj hr.1)) with hs|hs
      · have hc := Nat.find_min' hex ⟨lt_trans hj hr.1,hs⟩
        omega
      · exact hs
    · intro j hj hjn
      exact hr.2.trans (hX hj)
  · refine ⟨n,le_rfl,?_,?_⟩
    · intro j hj
      rcases not_splits S (X j) (hn j hj) with hs|hs
      · exact False.elim (hex ⟨j,hj,hs⟩)
      · exact hs
    · intro j hj hjn
      omega

lemma no_split_identity (hq : 0<q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ)
    (ψ : State L q) (n : ℕ) (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (S : Finset (Vertex L)) (H : Operator L q) (hH : SupportedOn H S)
    (hn : ∀ j, j<n → ¬Splits S (X j)) :
    let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
    let v := asMap (L := L) (q := q) P ψ
    inner ℂ v (asMap H v) = inner ℂ v (asMap (P*H) ψ) := by
  obtain ⟨r,hr,hi,ho⟩ := neutral_cut_index X hX S n hn
  exact neutral_identity hq X hX a ψ n F hF r hr H
    (fun j hj hjn => SupportedOn.mono (ho j hj hjn) hH)
    (fun j hj => commute_of_disjoint (hi j hj) H _ hH ⟨(F j).matrix,rfl⟩)

lemma edge_splits_iff (e : Edge L) (X : Finset (Vertex L)) :
    Splits (EdgeSites e) X ↔
      (e.val.1∈X ∧ e.val.2∉X) ∨ (e.val.1∉X ∧ e.val.2∈X) := by
  classical
  simp only [Splits,EdgeSites,Finset.mem_insert,Finset.mem_singleton]
  aesop

lemma crossing_edge_error (hq : 0<q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ)
    (ψ : State L q) (n : ℕ) (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k<n) (ha : 0<a k) (ha' : a k≤1/2)
    (e : Edge L) (hcut : Splits (EdgeSites e) (X k))
    (hunique : ∀ j, j<n → Splits (EdgeSites e) (X j) → j=k)
    (H : Operator L q) (hH : H.IsHermitian) (hHs : SupportedOn H (EdgeSites e)) :
    let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
    let v := asMap (L := L) (q := q) P ψ
    |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (P*H) ψ)).re| ≤
      8*(a k)^2*‖v‖^2*((q:ℝ)^2*opNorm H) := by
  have hout : ∀ j, k<j → j<n → SupportedOn H (X j) := by
    intro j hj hjn
    exact SupportedOn.mono (cross_outer_subset X hX _ n k hk hcut hunique j hj hjn) hHs
  have hin : ∀ j, j<k → Commute H (liftLocal (X j) (F j).matrix) := by
    intro j hj
    exact commute_of_disjoint (cross_inner_disjoint X hX _ n k hk hcut hunique j hj)
      H _ hHs ⟨(F j).matrix,rfl⟩
  let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
  let z := asMap (L := L) (q := q) P ψ
  have hbound (v w : Vertex L) (hs : EdgeSites e={v,w}) (hv : v∈X k) (hw : w∉X k) :
      |(inner ℂ z (asMap H z)).re-(inner ℂ z (asMap (P*H) ψ)).re| ≤
        8*(a k)^2*‖z‖^2*((q:ℝ)^2*opNorm H) := by
    obtain ⟨A,B,hdecomp,hcost⟩ := edge_decomposition hq e (X k) v w hs hv hw H hHs
    have hb := crossing_error_le hq X hX a ψ n F hF k hk ha ha' H hH hout hin A B hdecomp
    exact hb.trans (mul_le_mul_of_nonneg_left hcost (by positivity))
  rcases (edge_splits_iff e (X k)).mp hcut with h|h
  · exact hbound e.val.1 e.val.2 rfl h.1 h.2
  · exact hbound e.val.2 e.val.1 (by simp [EdgeSites,Finset.pair_comm]) h.2 h.1

lemma boundary_sum (X : Finset (Vertex L)) :
    (∑ e : Edge L, if Splits (EdgeSites e) X then (1:ℝ) else 0) = boundaryCard X := by
  classical
  simp only [edge_splits_iff,boundaryCard]
  simp [Fintype.card_subtype]

lemma crossing_budget_sum (X : ℕ → Finset (Vertex L)) (a : ℕ → ℝ) (n : ℕ) :
    (∑ e : Edge L, ∑ k : Fin n, if Splits (EdgeSites e) (X k) then (a k)^2 else 0) =
      ∑ k : Fin n, (a k)^2*(boundaryCard (X k):ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← boundary_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

lemma edge_error_budget (hq : 0<q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ)
    (ψ : State L q) (n : ℕ) (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (ha : ∀ k, k<n → 0<a k ∧ a k≤1/2)
    (e : Edge L) (hunique : ∀ j k, j<n → k<n →
      Splits (EdgeSites e) (X j) → Splits (EdgeSites e) (X k) → j=k)
    (H : Operator L q) (hH : H.IsHermitian) (hHs : SupportedOn H (EdgeSites e))
    (J : ℝ) (hJ : 0≤J) (hHJ : opNorm H≤J) :
    let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
    let v := asMap (L := L) (q := q) P ψ
    |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (P*H) ψ)).re| ≤
      (8*(q:ℝ)^2*J*‖v‖^2)*(∑ k : Fin n, if Splits (EdgeSites e) (X k) then (a k)^2 else 0) := by
  classical
  let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
  let v := asMap (L := L) (q := q) P ψ
  change |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (P*H) ψ)).re| ≤ _
  by_cases hex : ∃ k, k<n ∧ Splits (EdgeSites e) (X k)
  · obtain ⟨k,hk,hcut⟩ := hex
    have hb := crossing_edge_error hq X hX a ψ n F hF k hk (ha k hk).1 (ha k hk).2 e hcut
      (fun j hj hcutj => hunique j k hj hk hcutj hcut) H hH hHs
    have hsum : (a k)^2 ≤ ∑ j : Fin n, if Splits (EdgeSites e) (X j) then (a j)^2 else 0 := by
      calc
        _ = (if Splits (EdgeSites e) (X (⟨k,hk⟩:Fin n)) then (a (⟨k,hk⟩:Fin n))^2 else 0) := by simp [hcut]
        _ ≤ _ := Finset.single_le_sum (f := fun j : Fin n => if Splits (EdgeSites e) (X j) then (a j)^2 else 0)
          (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ (⟨k,hk⟩:Fin n))
    calc
      _ ≤ 8*(a k)^2*‖v‖^2*((q:ℝ)^2*opNorm H) := hb
      _ ≤ 8*(a k)^2*‖v‖^2*((q:ℝ)^2*J) := by gcongr
      _ = 8*(q:ℝ)^2*J*‖v‖^2*(a k)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  · have hn : ∀ k, k<n → ¬Splits (EdgeSites e) (X k) := by
      intro k hk hc
      exact hex ⟨k,hk,hc⟩
    have hz := no_split_identity hq X hX a ψ n F hF (EdgeSites e) H hHs hn
    change inner ℂ v (asMap H v)=inner ℂ v (asMap (P*H) ψ) at hz
    rw [hz,sub_self,abs_zero]
    positivity

theorem optimizer_excitation_bound (hq : 0<q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ)
    (Ω : State L q) (n : ℕ) (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer Ω (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (ha : ∀ k, k<n → 0<a k ∧ a k≤1/2)
    (hunique : ∀ e : Edge L, ∀ j k, j<n → k<n →
      Splits (EdgeSites e) (X j) → Splits (EdgeSites e) (X k) → j=k)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (hvs : ∀ v, SupportedOn (hv v) {v})
    (hes : ∀ e, SupportedOn (he e) (EdgeSites e)) (heH : ∀ e, (he e).IsHermitian)
    (J E₀ : ℝ) (hJ : 0≤J) (heJ : ∀ e, opNorm (he e)≤J)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω) :
    let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
    let v := asMap (L := L) (q := q) P Ω
    (inner ℂ v (asMap (Hamiltonian hv he) v)).re-E₀*‖v‖^2 ≤
      (8*(q:ℝ)^2*J*(∑ k : Fin n, (a k)^2*(boundaryCard (X k):ℝ)))*‖v‖^2 := by
  classical
  let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
  let v := asMap (L := L) (q := q) P Ω
  let h : Vertex L ⊕ Edge L → Operator L q := Sum.elim hv he
  let ε : Vertex L ⊕ Edge L → ℝ := Sum.elim (fun _ => 0) (fun e =>
    (8*(q:ℝ)^2*J*‖v‖^2)*(∑ k : Fin n, if Splits (EdgeSites e) (X k) then (a k)^2 else 0))
  have hh : ∑ i,h i = Hamiltonian hv he := by simp [h,Hamiltonian,Fintype.sum_sum_type]
  have herr (i : Vertex L ⊕ Edge L) :
      |(inner ℂ v (asMap (h i) v)).re-(inner ℂ v (asMap (P*h i) Ω)).re| ≤ ε i := by
    cases i with
    | inl z =>
      have hz := no_split_identity hq X hX a Ω n F hF {z} (hv z) (hvs z)
        (fun k hk => single_not_splits z (X k))
      change inner ℂ v (asMap (hv z) v)=inner ℂ v (asMap (P*hv z) Ω) at hz
      change |(inner ℂ v (asMap (hv z) v)).re-(inner ℂ v (asMap (P*hv z) Ω)).re| ≤ 0
      rw [hz,sub_self,abs_zero]
    | inr e =>
      exact edge_error_budget hq X hX a Ω n F hF ha e (hunique e) (he e) (heH e)
        (hes e) J hJ (heJ e)
  have hb := excitation_of_transition_errors h Ω E₀ (by simpa only [hh] using hg) P ε herr
  rw [hh] at hb
  have hsum : ∑ i,ε i=(8*(q:ℝ)^2*J*(∑ k : Fin n,(a k)^2*(boundaryCard (X k):ℝ)))*‖v‖^2 := by
    simp only [ε,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_const_zero,zero_add]
    rw [← Finset.mul_sum,crossing_budget_sum]
    ring
  exact hb.trans_eq hsum

end PolynomialPEPS.Subvolume.ContourEnergy

end

end OAI
