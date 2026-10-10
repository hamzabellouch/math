import OAI.MeasureTheory.Falconer.Estimates.ScalarPathCenters
import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialDyadic

namespace OAI

/-! The local scalar extraction on actual dyadic path children. Taking
 inverse images of selected centers retains the original child cells. -/
namespace Falconer.Regularization

 theorem scalar_initial_path_children {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hab : a ≤ b) (hb : b ≤ N) (p : CellPath 1)
    (hsize : 2050 ≤ (prefixChildren L a b p).card) :
    ∃ K ⊆ prefixChildren L a b p, ∃ k n : ℕ, 1 ≤ k ∧ K.card = 2^k ∧
      (prefixChildren L a b p).card ≤ 2050*K.card ∧ a+3 < n ∧ n+6 ≤ b ∧
      (∀ q ∈ K, ∀ r ∈ K, q ≠ r → 8*(1/2:ℝ)^n < |scalarPathCenter q-scalarPathCenter r|) ∧
      ∃ q ∈ K, ∃ r ∈ K, q ≠ r ∧ |scalarPathCenter q-scalarPathCenter r| ≤ 16*(1/2:ℝ)^n := by
  classical
  let C := prefixChildren L a b p
  let E := C.image scalarPathCenter
  have hlen := scalar_prefix_children_length (a := a) hL hb p
  have hinj := scalarPathCenter_injOn C hlen
  have hEc : E.card = C.card := Finset.card_image_of_injOn hinj
  have hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^b ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    exact scalarPathCenter_separated (hlen q hq) (hlen r hr)
      (fun heq => hxy (congrArg scalarPathCenter heq))
  have hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ (1/2:ℝ)^a := by
    intro x hx y hy
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hy
    exact scalarPathCenter_same_parent (hlen q hq) hab
      ((scalar_prefix_children_parent hab L p q hq).trans
        (scalar_prefix_children_parent hab L p r hr).symm)
  obtain ⟨F,hFE,k,n,hk,hFc,hcard,hn0,hn1,hsepF,q,hq,r,hr,hqr,hpair⟩ :=
    scalar_initial_dyadic_children E a b (by simpa only [hEc] using hsize) hsep hdiam
  obtain ⟨K,hKC,hKF⟩ := Finset.subset_image_iff.mp hFE
  have hKc : K.card = F.card := by
    rw [← hKF]
    exact (Finset.card_image_of_injOn (hinj.mono hKC)).symm
  have hKmem : ∀ q ∈ K, scalarPathCenter q ∈ F := by
    intro q hq
    rw [← hKF]
    exact Finset.mem_image_of_mem scalarPathCenter hq
  refine ⟨K,hKC,k,n,hk,hKc.trans hFc,?_,hn0,hn1,?_,?_⟩
  · simpa only [hEc,← hKc] using hcard
  · intro q hq r hr hqr
    exact hsepF _ (hKmem q hq) _ (hKmem r hr)
      (fun heq => hqr (hinj (hKC hq) (hKC hr) heq))
  · rw [← hKF] at hq hr
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r',hr',rfl⟩ := Finset.mem_image.mp hr
    exact ⟨q',hq',r',hr',fun heq => hqr (congrArg scalarPathCenter heq),hpair⟩

end Falconer.Regularization

end OAI
