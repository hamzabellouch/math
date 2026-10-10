import OAI.Analysis.TriangularHilbert.ErrorPairing

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

def hardKernel (r R t : ℝ) : ℝ :=
  ((if r < |t| then 1 else 0)-(if R < |t| then 1 else 0))/t

lemma hardKernel_decomposition {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) :
    smoothKernel (r^2) (R^2) t = kernelConstant*hardKernel r R t+endpointError r t-endpointError R t := by
  have hR := hr.trans_le hb
  by_cases ht : t = 0
  · subst t
    simp [smoothKernel,signedKernel,hardKernel,endpointError]
  unfold smoothKernel
  rw [smoothKernel_eq_profile (sq_pos_of_pos hr) (by nlinarith) ht,Real.sqrt_sq hr.le,Real.sqrt_sq hR.le]
  unfold endpointError errorProfile hardKernel
  simp only [abs_div,abs_of_pos hr,abs_of_pos hR,lt_div_iff₀ hr,lt_div_iff₀ hR,one_mul]
  split_ifs <;> ring

lemma selectedSum_le_no_finset (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    ‖selectedSum A h (fun m => h*(m:ℤ)) (fun i j => (r i j)^2) (fun i j => (R i j)^2)‖ ≤
      selectedConstant*arrayCubic A h := by
  classical
  let S : Finset ℝ := insert (h^2) ((Finset.univ.image (fun p : D×D => (r p.1 p.2)^2)) ∪
    (Finset.univ.image (fun p : D×D => (R p.1 p.2)^2)))
  apply selectedSum_le_cubic D A _ _ (fun i j => by have hh' := hr i j; have hb' := hb i j; nlinarith) S
    (Finset.insert_nonempty _ _) ?_ ?_ hh ?_
  · intro i j
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))
  · intro i j
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩))
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hs
    · rfl
    rcases Finset.mem_union.mp hs with hs|hs
    · rcases Finset.mem_image.mp hs with ⟨⟨i,j⟩,_,rfl⟩
      have hh' := hr i j
      nlinarith
    · rcases Finset.mem_image.mp hs with ⟨⟨i,j⟩,_,rfl⟩
      have hh' := (hr i j).trans (hb i j)
      nlinarith

def hardPairingConstant : ℝ := (selectedConstant+2*errorPairingConstant)/|kernelConstant|
lemma hardPairingConstant_pos : 0 < hardPairingConstant := by
  unfold hardPairingConstant
  exact div_pos (add_pos selectedConstant_pos (mul_pos (by norm_num) errorPairingConstant_pos)) (abs_pos.mpr kernelConstant_ne_zero)

lemma hardPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r R : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (hb : ∀ i j, r i j ≤ R i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => hardKernel (r i j) (R i j))‖ ≤
      hardPairingConstant*arrayCubic A h := by
  classical
  let u : D → ℝ := fun m => h*(m:ℤ)
  have he : (kernelConstant:ℂ)*kernelPairing A h u (fun i j => hardKernel (r i j) (R i j)) =
      selectedSum A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)-
        kernelPairing A h u (fun i j => endpointError (r i j))+
        kernelPairing A h u (fun i j => endpointError (R i j)) := by
    have hk : (fun i j => smoothKernel ((r i j)^2) ((R i j)^2)) = (fun i j t =>
        kernelConstant*hardKernel (r i j) (R i j) t+endpointError (r i j) t+-1*endpointError (R i j) t) := by
      funext i j t
      convert hardKernel_decomposition (hh.trans_le (hr i j)) (hb i j) t using 1
      ring
    have hs := kernelPairing_smooth A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)
    rw [hk,kernelPairing_add,kernelPairing_add,kernelPairing_const_mul,kernelPairing_const_mul] at hs
    push_cast at hs
    linear_combination hs
  have hn := (norm_add_le (selectedSum A h u (fun i j => (r i j)^2) (fun i j => (R i j)^2)-
      kernelPairing A h u (fun i j => endpointError (r i j)))
      (kernelPairing A h u (fun i j => endpointError (R i j)))).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  have h1 := selectedSum_le_no_finset D A hh r R hr hb
  have h2 := errorPairing_le D A hh r hr
  have h3 := errorPairing_le D A hh R (fun i j => (hr i j).trans (hb i j))
  have hden := abs_pos.mpr kernelConstant_ne_zero
  rw [hardPairingConstant,div_mul_eq_mul_div,le_div_iff₀ hden]
  dsimp [u] at hn
  nlinarith only [hn,h1,h2,h3]
end
end TriangularHilbert.Heat
end

end OAI
