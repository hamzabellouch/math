import Mathlib

namespace OAI

namespace SharpRamseyFive.PivotTree
open scoped Classical
noncomputable section
variable {w : ℕ}

def survivorRank (E : Finset (Fin w)) (v : Fin w) : Fin (w+1) :=
  ⟨(E.filter fun u=>u<v).card,by
    have h := (Finset.card_le_card (Finset.filter_subset (fun u=>u<v) E)).trans
      (Finset.card_le_univ E)
    simp only [Fintype.card_fin] at h
    omega⟩

lemma survivorRank_monotone (E : Finset (Fin w)) : Monotone (survivorRank E) := by
  intro i j hij
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter] at hu ⊢
  exact ⟨hu.1,lt_of_lt_of_le hu.2 hij⟩

lemma survivorRank_orderEmb (E : Finset (Fin w)) (j : Fin E.card) :
    (survivorRank E (E.orderEmbOfFin rfl j)).val=j.val := by
  have he : E.filter (fun u=>u<E.orderEmbOfFin rfl j)=
      (Finset.Iio j).image (E.orderEmbOfFin rfl) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_Iio]
    constructor
    · rintro ⟨hu,huj⟩
      let i := (E.orderIsoOfFin rfl).symm ⟨u,hu⟩
      have hi : E.orderEmbOfFin rfl i=u := congrArg Subtype.val
        ((E.orderIsoOfFin rfl).apply_symm_apply ⟨u,hu⟩)
      exact ⟨i,(E.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa only [hi] using huj),hi⟩
    · rintro ⟨i,hij,rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem ..,(E.orderEmbOfFin rfl).strictMono hij⟩
  change (E.filter _).card=j.val
  rw [he,Finset.card_image_of_injective _ (E.orderEmbOfFin rfl).injective]
  exact Fin.card_Iio j

lemma survivorRank_mem_lt (E : Finset (Fin w)) (v : Fin w) (hv : v∈E) :
    (survivorRank E v).val<E.card := by
  let j := (E.orderIsoOfFin rfl).symm ⟨v,hv⟩
  have hj : E.orderEmbOfFin rfl j=v := congrArg Subtype.val
    ((E.orderIsoOfFin rfl).apply_symm_apply ⟨v,hv⟩)
  rw [←hj,survivorRank_orderEmb]
  exact j.isLt

lemma survivorRank_original (E : Finset (Fin w)) (v : Fin w) (hv : v∈E) :
    E.orderEmbOfFin rfl ⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩=v := by
  let j := (E.orderIsoOfFin rfl).symm ⟨v,hv⟩
  have hj : E.orderEmbOfFin rfl j=v := congrArg Subtype.val
    ((E.orderIsoOfFin rfl).apply_symm_apply ⟨v,hv⟩)
  have he : (⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩ : Fin E.card)=j := by
    apply Fin.ext
    change (survivorRank E v).val=j.val
    rw [←hj,survivorRank_orderEmb]
  rw [he,hj]
end
end SharpRamseyFive.PivotTree

namespace SharpRamseyFive.Windows
open PivotTree
open scoped Classical
noncomputable section
lemma middleFirst_monotone (w n : ℕ) :
    Monotone (fun i : Fin (w*(2*n))=>(finProdFinEquiv.symm i : Fin w×Fin (2*n)).1) := by
  intro i j hij
  let a := (finProdFinEquiv.symm i : Fin w×Fin (2*n))
  let b := (finProdFinEquiv.symm j : Fin w×Fin (2*n))
  have hi : i.val=a.1.val*(2*n)+a.2.val := by
    calc
      _ = (finProdFinEquiv a).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i).symm
      _ = _ := by change a.2.val+(2*n)*a.1.val=_;ring
  have hj : j.val=b.1.val*(2*n)+b.2.val := by
    calc
      _ = (finProdFinEquiv b).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j).symm
      _ = _ := by change b.2.val+(2*n)*b.1.val=_;ring
  have h : a.1.val≤b.1.val := by
    by_contra hn
    have hg : (b.1.val+1)*(2*n)≤a.1.val*(2*n) := Nat.mul_le_mul_right (2*n) (by omega)
    have hb:=b.2.isLt
    have hij' : a.1.val*(2*n)+a.2.val≤b.1.val*(2*n)+b.2.val := by
      simpa only [Fin.le_def,hi,hj] using hij
    nlinarith
  exact h

lemma middleRank_monotone {w n : ℕ} (E : Finset (Fin w)) :
    Monotone (fun i : Fin (w*(2*n))=>survivorRank E
      (finProdFinEquiv.symm i : Fin w×Fin (2*n)).1) :=
  (survivorRank_monotone E).comp (middleFirst_monotone w n)
end
end SharpRamseyFive.Windows

end OAI
