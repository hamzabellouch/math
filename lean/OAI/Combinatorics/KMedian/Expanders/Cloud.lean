import Mathlib
import OAI.Combinatorics.KMedian.Expanders.GraphProducts
import OAI.Combinatorics.KMedian.Expanders.L2

namespace OAI

section Inline_PCPCloud

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type} [Fintype V] [Fintype D] [Nonempty D]
  [Fintype S] [Nonempty S]

noncomputable def average (f : V × D → ℝ) : V → ℝ := fun v => 𝔼 d, f (v,d)
def lift (f : V → ℝ) : V × D → ℝ := fun p => f p.1
noncomputable def residual (f : V × D → ℝ) : V × D → ℝ := fun p => f p-lift (average f) p

lemma lift_energy (f : V → ℝ) : energy (lift (D := D) f)=energy f := by
  unfold energy lift
  rw [expect_prod]
  simp only [Fintype.expect_const]

lemma lift_l2 (f : V → ℝ) : l2 (lift (D := D) f)=l2 f := by unfold l2; rw [lift_energy]

omit [Nonempty D] in
lemma average_mean (f : V × D → ℝ) : (𝔼 v, average f v) = 𝔼 p, f p :=
  (expect_prod f).symm

lemma average_energy (f : V × D → ℝ) : energy (average f) ≤ energy f := by
  unfold energy
  rw [expect_prod]
  apply expect_le_expect
  intro v _
  exact mean_sq_le_energy (fun d => f (v,d))

omit [Fintype V] in
lemma residual_mean (f : V × D → ℝ) (v : V) : (𝔼 d, residual f (v,d))=0 := by
  simp only [residual,lift,average]
  rw [expect_sub_distrib,Fintype.expect_const]
  ring

lemma residual_energy (f : V × D → ℝ) : energy (residual f)=energy f-energy (average f) := by
  unfold energy
  rw [expect_prod]
  have he (v : V) : (𝔼 d, residual f (v,d)^2)= (𝔼 d, f (v,d)^2)-(average f v)^2 :=
    energy_center (fun d => f (v,d))
  simp_rw [he]
  rw [expect_sub_distrib,← expect_prod (fun p : V × D => f p^2)]

lemma residual_energy_le (f : V × D → ℝ) : energy (residual f) ≤ energy f := by
  rw [residual_energy]
  linarith [energy_nonneg (average f)]

lemma average_l2 (f : V × D → ℝ) : l2 (average f) ≤ l2 f :=
  Real.sqrt_le_sqrt (average_energy f)
lemma residual_l2 (f : V × D → ℝ) : l2 (residual f) ≤ l2 f :=
  l2_mono _ _ (residual_energy_le f)

omit [Fintype V] [Nonempty D] in
lemma decompose (f : V × D → ℝ) : (fun p => lift (average f) p+residual f p)=f := by
  funext p
  unfold residual
  ring

omit [Fintype V] [Fintype D] [Nonempty D] [Nonempty S] in
lemma cloud_add (H : PortGraph D S) (f g : V × D → ℝ) :
    cloud H (fun p => f p+g p)=fun p => cloud H f p+cloud H g p := by
  funext p
  unfold cloud adjacency
  rw [expect_add_distrib]

omit [Fintype V] [Fintype D] [Nonempty D] in
lemma cloud_lift (H : PortGraph D S) (f : V → ℝ) : cloud H (lift f)=lift f := by
  funext p
  change (𝔼 _s : S, f p.1)=f p.1
  exact Fintype.expect_const _

omit [Fintype V] [Nonempty D] in
lemma cloud_decompose (H : PortGraph D S) (f : V × D → ℝ) :
    cloud H f=fun p => lift (average f) p+cloud H (residual f) p := by
  calc
    _ = cloud H (fun p => lift (average f) p+residual f p) := congrArg (cloud H) (decompose f).symm
    _ = _ := by rw [cloud_add,cloud_lift]

omit [Nonempty S] in
lemma cloud_residual_energy (H : PortGraph D S) {ρ : ℝ} (hH : H.Contracts ρ)
    (f : V × D → ℝ) : energy (cloud H (residual f)) ≤ ρ^2*energy (residual f) := by
  unfold energy
  rw [expect_prod,expect_prod,mul_expect]
  apply expect_le_expect
  intro v _
  exact hH (fun d => residual f (v,d)) (residual_mean f v)

omit [Nonempty S] in
lemma cloud_residual_l2 (H : PortGraph D S) {ρ : ℝ} (hρ : 0 ≤ ρ) (hH : H.Contracts ρ)
    (f : V × D → ℝ) : l2 (cloud H (residual f)) ≤ ρ*l2 (residual f) :=
  l2_le_of_energy_le hρ _ _ (cloud_residual_energy H hH f)

omit [Nonempty D] in
lemma cloud_energy_le (H : PortGraph D S) (f : V × D → ℝ) : energy (cloud H f) ≤ energy f := by
  unfold energy
  rw [expect_prod,expect_prod]
  apply expect_le_expect
  intro v _
  exact H.energy_adjacency_le (fun d => f (v,d))

omit [Nonempty D] in
lemma cloud_l2_le (H : PortGraph D S) (f : V × D → ℝ) : l2 (cloud H f) ≤ l2 f :=
  l2_mono _ _ (cloud_energy_le H f)

omit [Fintype V] [Fintype D] [Nonempty D] in
lemma permute_add (G : PortGraph V D) (f g : V × D → ℝ) :
    permute G (fun p => f p+g p)=fun p => permute G f p+permute G g p := rfl

omit [Nonempty D] in
lemma permute_energy (G : PortGraph V D) (f : V × D → ℝ) : energy (permute G f)=energy f := by
  unfold energy permute
  exact Fintype.expect_equiv G.rotate _ _ (fun _ => rfl)

omit [Nonempty D] in
lemma permute_l2 (G : PortGraph V D) (f : V × D → ℝ) : l2 (permute G f)=l2 f := by
  unfold l2
  rw [permute_energy]

omit [Fintype V] [Nonempty D] in
lemma average_permute_lift (G : PortGraph V D) (f : V → ℝ) :
    average (permute G (lift f))=G.adjacency f := rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPCloud

end OAI
