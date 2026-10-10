import Mathlib
import OAI.Probability.LogConcave.Sampling.ConditionalFieldMean
import OAI.Probability.LogConcave.JetEstimates.Extension

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

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def conditionalSlotEmbedding {ι : Type*} (d : ℕ) (s : ι → Bool) :
    (ι → Fin d) ↪ (ι → Fin d ⊕ Fin d) where
  toFun a i := if s i then Sum.inr (a i) else Sum.inl (a i)
  inj' := by
    intro a c h
    funext i
    have hi := congrFun h i
    cases hs : s i <;> simpa [hs] using hi

theorem conditional_cumulant_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {ι ϑ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
    (s : ι → Bool) (t : ϑ → Bool) (l : List ι) (k : List ϑ)
    (hlN : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hkN : k.Nodup) (hkall : k.toFinset=Finset.univ) (hlne : l≠[]) (hkne : k≠[]) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    let b := EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    TensorEnergy.Bound (fun (a : ι → Fin d) (c : ϑ → Fin d) =>
      JetCalculus.mixedJet (fun i => b (conditionalSlotEmbedding d s a i))
        (fun j => b (conditionalSlotEmbedding d t c j)) l k
        (fun z => Real.log (Appell.laplace μ (fun _ => (1:ℝ)) (z.1+z.2))))
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        Appell.splitConstant (2*Real.pi^2*(1-ρ^2)) (Fintype.card ι) (Fintype.card ϑ)) := by
  obtain ⟨hp,hm,hP⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  have hβ : 0 ≤ 2*Real.pi^2*(1-ρ^2) := by
    obtain ⟨ha,_⟩ := probability_time hρ0 hρ1
    positivity
  exact (Appell.actual_cumulant_energy hm hβ hP
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) l k hlN hlall hkN hkall hlne hkne).submatrix
    (conditionalSlotEmbedding d s) (conditionalSlotEmbedding d t)

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def conditionalU {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y u : Point d) (L : ℝ) {ι : Type*} (v : ι → Point d) (l : List ι) : ℝ :=
  L/(1-ρ^2)^l.length * JetCalculus.jet (fun i => jointPosition d (v i)) l
    (JetCalculus.dir (jointField d u)
      (fun θ => Real.log (Appell.laplace (jointConditionalLaw F x r ρ y L)
        (fun _ => (1:ℝ)) θ))) 0

lemma conditionalFieldMean_jet_U {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (u y : Point d) {ι : Type*} (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l
      (conditionalMeanScalar F x r ρ (fun z => inner ℝ u (primitiveField F x r z))) y=
      ρ^l.length*conditionalU F x r ρ y u ((lam:ℝ)*r) v l := by
  rw [conditionalFieldMean_jet hF x hr hlam hl hρ0 hρ1 u y v l]
  simp only [conditionalU,div_pow]
  ring

theorem conditional_jet_cumulant_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {ι ϑ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
    (s : ι → Bool) (t : ϑ → Bool) (l : List ι) (k : List ϑ)
    (hlN : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hkN : k.Nodup) (hkall : k.toFinset=Finset.univ) (hlne : l≠[]) (hkne : k≠[])
    (o : List (ι ⊕ ϑ)) (ho : o.Perm (l.map Sum.inl++k.map Sum.inr)) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    let b := EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    TensorEnergy.Bound (fun (a : ι → Fin d) (c : ϑ → Fin d) =>
      JetCalculus.jet (Sum.elim (fun i => b (conditionalSlotEmbedding d s a i))
        (fun j => b (conditionalSlotEmbedding d t c j))) o
        (fun z => Real.log (Appell.laplace μ (fun _ => (1:ℝ)) z)) 0)
      (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
        Appell.splitConstant (2*Real.pi^2*(1-ρ^2)) (Fintype.card ι) (Fintype.card ϑ)) := by
  obtain ⟨hp,hm,hP⟩ := jointConditionalLaw_properties hF x hr hlam hl hρ0 hρ1 y
  let := hp
  have hβ : 0 ≤ 2*Real.pi^2*(1-ρ^2) := by
    obtain ⟨ha,_⟩ := probability_time hρ0 hρ1
    positivity
  exact (Appell.actual_jet_cumulant_energy hm hβ hP
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) l k hlN hlall hkN hkall hlne hkne o ho).submatrix
    (conditionalSlotEmbedding d s) (conditionalSlotEmbedding d t)

lemma normalized_energy_factor {a : ℝ} (ha : a≠0) (B : ℝ) {j k : ℕ}
    (hj : 0<j) (hk : 0<k) :
    ((a^(j+k-1))⁻¹)^2*(B*a)^(j+k)=B^(j+k)/(a^(j+k-2)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h1 : j.succ+k.succ-1=j+k+1 := by omega
  have h2 : j.succ+k.succ-2=j+k := by omega
  have h3 : j.succ+k.succ=(j+k)+2 := by omega
  rw [h1,h2,h3,mul_pow]
  simp only [pow_add,pow_one,pow_two]
  field_simp

theorem conditional_normalized_tensor_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d)
    {ι ϑ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ϑ] [DecidableEq ϑ]
    (s : ι → Bool) (t : ϑ → Bool) (l : List ι) (k : List ϑ)
    (hlN : l.Nodup) (hlall : l.toFinset=Finset.univ)
    (hkN : k.Nodup) (hkall : k.toFinset=Finset.univ) (hlne : l≠[]) (hkne : k≠[])
    (o : List (ι ⊕ ϑ)) (ho : o.Perm (l.map Sum.inl++k.map Sum.inr)) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    let b := EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ
    let n := Fintype.card ι+Fintype.card ϑ
    TensorEnergy.Bound (fun (a : ι → Fin d) (c : ϑ → Fin d) =>
      ((1-ρ^2)^(n-1))⁻¹ * JetCalculus.jet (Sum.elim (fun i => b (conditionalSlotEmbedding d s a i))
        (fun j => b (conditionalSlotEmbedding d t c j))) o
        (fun z => Real.log (Appell.laplace μ (fun _ => (1:ℝ)) z)) 0)
      (((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n *
        (((Fintype.card ι).factorial:ℝ)*((Fintype.card ϑ).factorial:ℝ))^2 /
          (1-ρ^2)^(n-2)) := by
  dsimp only
  have hj : 0<Fintype.card ι := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i,_⟩ := List.exists_mem_of_ne_nil l hlne
    exact ⟨i⟩
  have hk : 0<Fintype.card ϑ := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i,_⟩ := List.exists_mem_of_ne_nil k hkne
    exact ⟨i⟩
  have hb := (conditional_jet_cumulant_energy hF x hr hlam hl hρ0 hρ1 y
    s t l k hlN hlall hkN hkall hlne hkne o ho).smul
      (((1-ρ^2)^(Fintype.card ι+Fintype.card ϑ-1))⁻¹)
  convert! hb using 1
  dsimp [Appell.splitConstant]
  have he := normalized_energy_factor (probability_time hρ0 hρ1).1.ne' (2*Real.pi^2) hj hk
  calc
    _ = (((Fintype.card ι+Fintype.card ϑ+1:ℕ):ℝ)^(2*(Fintype.card ι+Fintype.card ϑ+1)) *
      (((Fintype.card ι).factorial:ℝ)*((Fintype.card ϑ).factorial:ℝ))^2) *
      ((2*Real.pi^2)^(Fintype.card ι+Fintype.card ϑ)/(1-ρ^2)^(Fintype.card ι+Fintype.card ϑ-2)) := by ring
    _ = _ := by rw [←he]; ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
