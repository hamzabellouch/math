import Mathlib
import OAI.Probability.LogConcave.JetEstimates.AssignmentsFinset
import OAI.Probability.LogConcave.JetEstimates.MixedJetAdd

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.Appell
open MeasureTheory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι ϑ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
  [Fintype κ]

theorem actual_jet_cumulant_energy {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : HasExpMoments μ) {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (b : OrthonormalBasis κ ℝ E) (l : List ι) (k : List ϑ)
    (hl : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hk : k.Nodup) (hkall : k.toFinset=Finset.univ)
    (hlne : l≠[]) (hkne : k≠[]) (o : List (ι ⊕ ϑ))
    (ho : o.Perm (l.map Sum.inl++k.map Sum.inr)) :
    TensorEnergy.Bound (fun (a : ι → κ) (c : ϑ → κ) =>
      JetCalculus.jet (Sum.elim (fun i => b (a i)) (fun j => b (c j))) o
        (fun θ => Real.log (laplace μ (fun _ => (1:ℝ)) θ)) 0)
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        splitConstant β (Fintype.card ι) (Fintype.card ϑ)) := by
  classical
  have hs := (contDiff_laplace hμ continuous_const (HasGrowth.const (1:ℝ))).log
    (fun θ => (laplace_one_pos hμ θ).ne')
  simp_rw [JetCalculus.jet_perm hs _ ho, ← JetCalculus.mixedJet_add hs]
  exact actual_cumulant_energy hμ hβ hP b l k hl hlall hk hkall hlne hkne

end LogConcaveSampling.Appell

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

noncomputable def zeroExtension (e : K ↪ I) (v : K → ℝ) (i : I) : ℝ := by
  classical
  exact ∑ k, if e k=i then v k else 0

omit [Fintype I] in
lemma zeroExtension_apply (e : K ↪ I) (v : K → ℝ) (k : K) :
    zeroExtension e v (e k)=v k := by
  classical
  simp [zeroExtension,e.injective.eq_iff]

lemma dot_zeroExtension (e : K ↪ I) (v : K → ℝ) (g : I → ℝ) :
    (∑ i, g i*zeroExtension e v i)=∑ k,g (e k)*v k := by
  classical
  simp only [zeroExtension,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_ite]

lemma energy_zeroExtension (e : K ↪ I) (v : K → ℝ) :
    (∑ i, (zeroExtension e v i)^2)=∑ k,(v k)^2 := by
  simp only [pow_two]
  rw [dot_zeroExtension]
  simp only [zeroExtension_apply]

lemma Bound.submatrix {A : I → J → ℝ} {C : ℝ} (h : Bound A C)
    (e : K ↪ I) (f : L ↪ J) : Bound (fun k l => A (e k) (f l)) C := by
  classical
  intro v
  have hh := h (zeroExtension f v)
  simp only [dot_zeroExtension,energy_zeroExtension] at hh
  apply le_trans _ hh
  let g : I → ℝ := fun i => (∑ l,A i (f l)*v l)^2
  change (∑ k,g (e k)) ≤ ∑ i,g i
  rw [← Finset.sum_image (s := Finset.univ) (f := g) e.injective.injOn]
  apply Finset.sum_le_univ_sum_of_nonneg
  intro i
  exact sq_nonneg _

end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
