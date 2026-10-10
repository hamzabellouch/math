import OAI.NumberTheory.SingleFold.QuadraticHeight

namespace OAI

namespace SingleFold.HeightDescent

universe u

variable {A : Type u} [AddCommGroup A]

theorem finitely_generated (h : A → ℝ) [Northcott h]
    (hn : ∀ P, 0 ≤ h P)
    (hp : ∀ P Q, h (P+Q)+h (P-Q)=2*h P+2*h Q)
    (hd : ∀ P, h ((2:ℕ) • P)=4*h P)
    (F : Finset A) (hF : ∀ P, ∃ R ∈ F, ∃ Q, P=R+(2:ℕ) • Q) : AddGroup.FG A := by
  classical
  obtain ⟨B,hB⟩ := (F.finite_toSet.image h).bddAbove
  let S : Set A := {P | h P ≤ B}
  have hS : S.Finite := Northcott.finite_le B
  have hR : ∀ R ∈ F, R ∈ AddSubgroup.closure S := by
    intro R hR
    apply AddSubgroup.subset_closure
    exact hB ⟨R,hR,rfl⟩
  have htop : AddSubgroup.closure S = ⊤ := by
    apply top_unique
    intro P _
    by_contra hh
    obtain ⟨P,hP,hmin⟩ := Northcott.exists_min_image h {P | P ∉ AddSubgroup.closure S} ⟨P,hh⟩
    have hPl : B < h P := by
      by_contra hle
      exact hP (AddSubgroup.subset_closure (le_of_not_gt hle))
    obtain ⟨R,hRF,Q,hPQ⟩ := hF P
    have hRB : h R ≤ B := hB ⟨R,hRF,rfl⟩
    have he : P-R=(2:ℕ) • Q := by rw [hPQ]; abel
    have hdQ : 4*h Q ≤ 2*h P+2*h R := by
      have hpara := hp P R
      rw [he,hd] at hpara
      linarith [hn (P+R)]
    have hsmall : h Q < h P := by linarith
    have hQ : Q ∈ AddSubgroup.closure S := by
      by_contra hQ
      have := hmin Q hQ
      linarith
    apply hP
    rw [hPQ]
    exact (AddSubgroup.closure S).add_mem (hR R hRF)
      ((AddSubgroup.closure S).nsmul_mem hQ 2)
  exact ⟨hS.toFinset, by simpa only [Set.Finite.coe_toFinset] using htop⟩

end SingleFold.HeightDescent

namespace SingleFold.CurveRank
open Descent

instance : Northcott CurveHeight.canonicalHeight where
  finite_le B := by
    obtain ⟨c,hc,hbound⟩ := CurveHeight.uniform_height
    apply (Northcott.finite_le (h := CurveHeight.naiveHeight) (2*B+c)).subset
    intro P hP
    have hh := (abs_le.mp (hbound P)).2
    change CurveHeight.canonicalHeight P ≤ B at hP
    change CurveHeight.naiveHeight P ≤ 2*B+c
    linarith

lemma canonical_parallelogram (P Q : E.Point) :
    CurveHeight.canonicalHeight (P+Q) + CurveHeight.canonicalHeight (P-Q) =
      2*CurveHeight.canonicalHeight P + 2*CurveHeight.canonicalHeight Q := by
  obtain ⟨C,hC⟩ := CurveHeight.approximate_parallelogram
  have hh := QuadraticLimit.limit_parallelogram CurveHeight.naiveHeight C
    CurveHeight.naiveHeight_zero hC P Q
  unfold CurveHeight.canonicalHeight
  convert congrArg (fun x : ℝ => (1/2:ℝ)*x) hh using 1 <;> ring

noncomputable def representatives : Finset E.Point := by
  classical
  exact {0,T0,T5,T0+T5} ∪ (({0,T0,T5,T0+T5} : Finset E.Point).image (· + G))

lemma representatives_card : representatives.card ≤ 8 := by
  classical
  have hu := Finset.card_union_le ({0,T0,T5,T0+T5} : Finset E.Point)
    (({0,T0,T5,T0+T5} : Finset E.Point).image (· + G))
  have hi := Finset.card_image_le (s := ({0,T0,T5,T0+T5} : Finset E.Point)) (f := (· + G))
  have hc : ({0,T0,T5,T0+T5} : Finset E.Point).card ≤ 4 := by
    exact (Finset.card_insert_le ..).trans (by
      have h1 := Finset.card_insert_le T0 ({T5,T0+T5} : Finset E.Point)
      have h2 := Finset.card_insert_le T5 ({T0+T5} : Finset E.Point)
      simp only [Finset.card_singleton] at h2
      omega)
  unfold representatives
  omega

lemma representatives_cover (P : E.Point) : ∃ R ∈ representatives, ∃ Q, P=R+(2:ℕ) • Q := by
  classical
  obtain ⟨S,b,Q,hS,hP⟩ := mod_two_cover P
  have hmem : S ∈ ({0,T0,T5,T0+T5} : Finset E.Point) := by simpa using hS
  refine ⟨S+(if b then G else 0),?_,Q,hP⟩
  cases b
  · simpa only [representatives,Bool.false_eq_true,↓reduceIte,add_zero] using Finset.mem_union_left
      (({0,T0,T5,T0+T5} : Finset E.Point).image (· + G)) hmem
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S,hmem,rfl⟩)

instance : AddGroup.FG E.Point :=
  HeightDescent.finitely_generated CurveHeight.canonicalHeight CurveHeight.canonicalHeight_nonneg
    canonical_parallelogram
    (fun P => by convert CurveHeight.canonicalHeight_nsmul P 2 using 1; norm_num)
    representatives representatives_cover

end SingleFold.CurveRank

end OAI
