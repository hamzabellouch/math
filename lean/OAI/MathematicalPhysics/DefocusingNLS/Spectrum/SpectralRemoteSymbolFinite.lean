import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolBilinear

namespace OAI

/-! Finite coordinate assemblies preserve uniform logarithmic symbols. -/

open Set Filter Topology
namespace DefocusingNLS
namespace HasUniformLogJetBound

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {L : ℕ → ℝ} {sigma : ℝ}

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ → A)
    (hf : ∀ i ∈ s, HasUniformLogJetBound L sigma (f i)) :
    HasUniformLogJetBound L sigma (fun n t => ∑ i ∈ s, f i n t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HasUniformLogJetBound.zero (L := L) sigma :
      HasUniformLogJetBound L sigma (fun _ _ => (0 : A)))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self _ _)).add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℕ → ℝ → ι → A} (hf : ∀ i, HasUniformLogJetBound L sigma (fun n t => f n t i)) :
    HasUniformLogJetBound L sigma f := by
  have hh := HasUniformLogJetBound.sum Finset.univ
    (fun i n t => (ContinuousLinearMap.single ℝ (fun _ : ι => A) i) (f n t i))
    (fun i _ => (hf i).map (ContinuousLinearMap.single ℝ (fun _ : ι => A) i))
  convert hh using 1
  funext n t i
  simp only [Finset.sum_apply,ContinuousLinearMap.single_apply]
  simp

end HasUniformLogJetBound
end DefocusingNLS

end OAI
