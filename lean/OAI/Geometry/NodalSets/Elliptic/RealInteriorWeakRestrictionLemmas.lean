import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakProduct

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

theorem real_interior_weak_restrict {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hL : MeasurableSet L) (hsub : K ⊆ L)
    (u g : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict L))
    (hg : MemLp g 2 (volume.restrict L)) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∫ x in L, u x*coordPartial psi x i)=-(∫ x in L, g x*psi x)) :
    MemLp u 2 (volume.restrict K) ∧ MemLp g 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ u x*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ g x*psi x) K ∧
      (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x) := by
  have huK := hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgK := hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨huK,hgK,fun psi hp hc hs ↦ ?_⟩
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  have h := hweak psi hp hc (hs.trans hsub)
  have he1 : (∫ x in L, u x*coordPartial psi x i)=∫ x in K, u x*coordPartial psi x i := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y i)
      (fun ht ↦ hx.2 (hs (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) ht))),mul_zero]
  have he2 : (∫ x in L, g x*psi x)=∫ x in K, g x*psi x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx.2 (hs ht)),mul_zero]
  rw [he1,he2] at h
  exact ⟨huK.integrable_mul hdt,hgK.integrable_mul ht,h⟩

theorem real_interior_weak_sum {n : ℕ} {I : Type*} [Fintype I]
    {K : Set (Coord n)} (hK : IsCompact K) (u g : I → Coord n → ℝ)
    (hu : ∀ a, MemLp (u a) 2 (volume.restrict K))
    (hg : ∀ a, MemLp (g a) 2 (volume.restrict K)) (i : Fin n)
    (hweak : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u a x*coordPartial psi x i)=-(∫ x in K, g a x*psi x)) :
    MemLp (fun x ↦ ∑ a, u a x) 2 (volume.restrict K) ∧
    MemLp (fun x ↦ ∑ a, g a x) 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (∑ a, u a x)*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ (∑ a, g a x)*psi x) K ∧
      (∫ x in K, (∑ a, u a x)*coordPartial psi x i)=-(∫ x in K, (∑ a, g a x)*psi x) := by
  have hsu : MemLp (fun x ↦ ∑ a, u a x) 2 (volume.restrict K) := memLp_finsetSum _ (fun a _ ↦ hu a)
  have hsg : MemLp (fun x ↦ ∑ a, g a x) 2 (volume.restrict K) := memLp_finsetSum _ (fun a _ ↦ hg a)
  refine ⟨hsu,hsg,fun psi hp hc hs ↦ ?_⟩
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  refine ⟨hsu.integrable_mul hdt,hsg.integrable_mul ht,?_⟩
  have hiu (a : I) : IntegrableOn (fun x ↦ u a x*coordPartial psi x i) K := (hu a).integrable_mul hdt
  have hig (a : I) : IntegrableOn (fun x ↦ g a x*psi x) K := (hg a).integrable_mul ht
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun a _ ↦ hiu a),
    integral_finsetSum Finset.univ (fun a _ ↦ hig a)]
  simp only [hweak _ psi hp hc hs,Finset.sum_neg_distrib]

theorem real_weak_equation_differentiation {n : ℕ} {K : Set (Coord n)}
    (hK : IsCompact K) (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (F : Coord n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j))
    (hU : ∀ a, MemLp (U a) 2 (volume.restrict K))
    (hH : ∀ a k, MemLp (H a k) 2 (volume.restrict K))
    (hF : MemLp F 2 (volume.restrict K))
    (hweak : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x k)=-(∫ x in K, H a k x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∑ a, ∑ j, ∫ x in K, C x a j*U a x*coordPartial psi x j)=∫ x in K, F x*psi x)
    (k : Fin n) (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ K) :
    (∀ a j, IntegrableOn (fun x ↦ C x a j*H a k x*coordPartial psi x j) K ∧
      IntegrableOn (fun x ↦ coordPartial (fun y ↦ C y a j) x k*U a x*coordPartial psi x j) K) ∧
    IntegrableOn (fun x ↦ F x*coordPartial psi x k) K ∧
    (∑ a, ∑ j, ∫ x in K, C x a j*H a k x*coordPartial psi x j) =
      -(∫ x in K, F x*coordPartial psi x k) -
        ∑ a, ∑ j, ∫ x in K, coordPartial (fun y ↦ C y a j) x k*U a x*coordPartial psi x j := by
  have hd (j : Fin n) := real_coordPartial_smooth psi hp j
  have hdc (j : Fin n) : HasCompactSupport (fun x ↦ coordPartial psi x j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ (Pi.single j 1))
  have hds (j : Fin n) : tsupport (fun x ↦ coordPartial psi x j) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hs
  have hdLp (j : Fin n) := real_continuous_memLp_compact hK _ (hd j).continuous
  have hi (a j : Fin n) :
      IntegrableOn (fun x ↦ C x a j*H a k x*coordPartial psi x j) K ∧
      IntegrableOn (fun x ↦ coordPartial (fun y ↦ C y a j) x k*U a x*coordPartial psi x j) K := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hK _ (hC a j).continuous
    obtain ⟨_,_,hdb⟩ := real_compact_multiplier_bound hK _
      (real_coordPartial_smooth _ (hC a j) k).continuous
    exact ⟨((hb _ (hH a k)).1).integrable_mul (hdLp j),
      ((hdb _ (hU a)).1).integrable_mul (hdLp j)⟩
  have he (a j : Fin n) :
      (∫ x in K, C x a j*U a x*coordPartial (fun y ↦ coordPartial psi y k) x j) =
        -((∫ x in K, C x a j*H a k x*coordPartial psi x j) +
          (∫ x in K, coordPartial (fun y ↦ C y a j) x k*U a x*coordPartial psi x j)) := by
    have hw := (real_interior_weak_product hK (U a) (H a k) (fun x ↦ C x a j)
      (hU a) (hH a k) (hC a j) k (hweak a k)).2.2
      (fun x ↦ coordPartial psi x j) (hd j) (hdc j) (hds j)
    have hcmm : (fun x ↦ (C x a j*U a x)*coordPartial (fun y ↦ coordPartial psi y j) x k) =
        fun x ↦ C x a j*U a x*coordPartial (fun y ↦ coordPartial psi y k) x j := by
      funext x
      rw [real_coordPartial_commute psi hp x k j]
    rw [hcmm] at hw
    rw [hw.2.2]
    congr 1
    simp_rw [add_mul]
    exact integral_add (hi a j).1 (hi a j).2
  have ht := heq (fun x ↦ coordPartial psi x k) (hd k) (hdc k) (hds k)
  simp_rw [he,Finset.sum_neg_distrib,Finset.sum_add_distrib] at ht
  exact ⟨hi,hF.integrable_mul (hdLp k),by linarith only [ht]⟩

def realWeakFourJet (w : Coord 4 → ℝ) (U : Fin 4 → Coord 4 → ℝ)
    (H : Fin 4 → Fin 4 → Coord 4 → ℝ) (J : Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ)
    (L : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ) : List (Fin 4) → Coord 4 → ℝ
  | [] => w
  | [a] => U a
  | [k,a] => H a k
  | [l,k,a] => J a k l
  | [i,l,k,a] => L a k l i
  | _ => 0

theorem real_weak_four_jet_bounds {Q : Set (Coord 4)}
    (w : Coord 4 → ℝ) (U : Fin 4 → Coord 4 → ℝ)
    (H : Fin 4 → Fin 4 → Coord 4 → ℝ) (J : Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ)
    (L : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ) (E : ℝ)
    (hw : MemLp w 2 (volume.restrict Q) ∧ (∫ x in Q, (w x)^2) ≤ E)
    (hU : ∀ a, MemLp (U a) 2 (volume.restrict Q) ∧ (∫ x in Q, (U a x)^2) ≤ E)
    (hH : ∀ a k, MemLp (H a k) 2 (volume.restrict Q) ∧ (∫ x in Q, (H a k x)^2) ≤ E)
    (hJ : ∀ a k l, MemLp (J a k l) 2 (volume.restrict Q) ∧ (∫ x in Q, (J a k l x)^2) ≤ E)
    (hL : ∀ a k l i, MemLp (L a k l i) 2 (volume.restrict Q) ∧ (∫ x in Q, (L a k l i x)^2) ≤ E)
    (ds : List (Fin 4)) (hd : ds.length ≤ 4) :
    MemLp (realWeakFourJet w U H J L ds) 2 (volume.restrict Q) ∧
      (∫ x in Q, (realWeakFourJet w U H J L ds x)^2) ≤ E := by
  rcases ds with _ | ⟨i, _ | ⟨l, _ | ⟨k, _ | ⟨a, _ | ⟨b,bs⟩⟩⟩⟩⟩
  · exact hw
  · exact hU i
  · exact hH l i
  · exact hJ k l i
  · exact hL a k l i
  · simp only [List.length_cons] at hd; omega

theorem real_weak_four_jet_pairings {Q : Set (Coord 4)}
    (w : Coord 4 → ℝ) (U : Fin 4 → Coord 4 → ℝ)
    (H : Fin 4 → Fin 4 → Coord 4 → ℝ) (J : Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ)
    (L : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ)
    (hw : ∀ i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, w x*coordPartial psi x i)=-(∫ x in Q, U i x*psi x))
    (hU : ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U a x*coordPartial psi x i)=-(∫ x in Q, H a i x*psi x))
    (hH : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, H a k x*coordPartial psi x i)=-(∫ x in Q, J a k i x*psi x))
    (hJ : ∀ a k l i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, J a k l x*coordPartial psi x i)=-(∫ x in Q, L a k l i x*psi x))
    (ds : List (Fin 4)) (hd : ds.length ≤ 3) (i : Fin 4)
    (psi : Coord 4 → ℝ) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, realWeakFourJet w U H J L ds x*coordPartial psi x i) =
      -(∫ x in Q, realWeakFourJet w U H J L (i::ds) x*psi x) := by
  rcases ds with _ | ⟨l, _ | ⟨k, _ | ⟨a, _ | ⟨b,bs⟩⟩⟩⟩
  · exact hw i psi hp hc hs
  · exact hU l i psi hp hc hs
  · exact hH k l i psi hp hc hs
  · exact hJ a k l i psi hp hc hs
  · simp only [List.length_cons] at hd; omega

end Yau

end

end OAI
