import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteNashCoverAffine
import OAI.Analysis.SymmetricDomains.VerticalPieceBasePolynomial

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

namespace SemialgebraicOn
lemma sub {ι κ : Type*} [Finite κ] {B : Set (ι → ℝ)} {f g : (ι → ℝ) → (κ → ℝ)}
    (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x - g x) := by
  have hp := (polynomial (B := (univ : Set ((κ ⊕ κ) → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inr j))).comp
      (hf.pair hg) (fun _ _ => mem_univ _)
  exact hp.congr (fun x _ => by ext j; simp)
end SemialgebraicOn

lemma hasFiniteNashCover_verticalPiece {n r : ℕ}
    (H : ∀ k (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin k → ℝ)),
      SemialgebraicOn B f → HasAnalyticNashCover B f)
    {B : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin r → ℝ)}
    (hs : SemialgebraicOn B f) (p : VerticalPiece r)
    (hne : ∀ x ∈ B, (verticalPieceSet (f x) p).Nonempty) :
    HasFiniteNashCover {y : Fin (n+1) → ℝ | Fin.tail y ∈ B ∧ y 0 ∈ verticalPieceSet (f (Fin.tail y)) p} := by
  have hB := hs.domain
  have hsIoi : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) (Ioi 0) := by
    convert (PolynomialSignSet.positive (c := fun t : ℝ => fun _ : Fin 1 => t) (MvPolynomial.X 0)) using 1
    ext t
    simp
  have hsIoo : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) (Ioo 0 1) := by
    have hu := PolynomialSignSet.positive (c := fun t : ℝ => fun _ : Fin 1 => t)
      (MvPolynomial.C 1 - MvPolynomial.X 0)
    convert hsIoi.inter hu using 1
    ext t
    simp [sub_pos]
  rcases p with i | ⟨l,u⟩
  · have ha := hs.reindex (fun _ : Fin 1 => i)
    simpa only [verticalPieceSet,mem_singleton_iff] using hasFiniteNashCover_graph ha (H 1 B _ ha)
  · cases l with
    | none =>
      cases u with
      | none =>
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun _ => Fin.cons 0 (fun _ => 1)
        have hg : SemialgebraicOn B g := SemialgebraicOn.constant hB _
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg) (by intro x hx; norm_num [g])
          univ isOpen_univ isConnected_univ PolynomialSignSet.univ
        convert hh using 1
        ext y
        simp [verticalPieceSet,g]
      | some j =>
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun x => Fin.cons (f x j) (fun _ => -1)
        have hg : SemialgebraicOn B g := (hs.reindex (fun _ : Fin 1 => j)).finCons
          (SemialgebraicOn.constant hB (fun _ : Fin 1 => -1))
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg) (by intro x hx; norm_num [g])
          (Ioi 0) isOpen_Ioi isConnected_Ioi hsIoi
        convert hh using 1
        ext y
        simp only [mem_ofPred_eq,verticalPieceSet,mem_Iio,mem_Ioi,g,Fin.cons_zero,Fin.cons_one,neg_mul,one_mul]
        constructor
        · rintro ⟨hy,hlt⟩
          exact ⟨hy,f (Fin.tail y) j-y 0,by linarith,by ring⟩
        · rintro ⟨hy,t,ht,he⟩
          exact ⟨hy,by linarith⟩
    | some i =>
      cases u with
      | none =>
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun x => Fin.cons (f x i) (fun _ => 1)
        have hg : SemialgebraicOn B g := (hs.reindex (fun _ : Fin 1 => i)).finCons
          (SemialgebraicOn.constant hB (fun _ : Fin 1 => 1))
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg) (by intro x hx; norm_num [g])
          (Ioi 0) isOpen_Ioi isConnected_Ioi hsIoi
        convert hh using 1
        ext y
        simp only [mem_ofPred_eq,verticalPieceSet,mem_Ioi,g,Fin.cons_zero,Fin.cons_one,one_mul]
        constructor
        · rintro ⟨hy,hlt⟩
          exact ⟨hy,y 0-f (Fin.tail y) i,by linarith,by ring⟩
        · rintro ⟨hy,t,ht,he⟩
          exact ⟨hy,by linarith⟩
      | some j =>
        have hlt (x) (hx : x ∈ B) : f x i < f x j := nonempty_Ioo.mp (hne x hx)
        let g : (Fin n → ℝ) → (Fin 2 → ℝ) := fun x => Fin.cons (f x i) (fun _ => f x j-f x i)
        have hg : SemialgebraicOn B g := (hs.reindex (fun _ : Fin 1 => i)).finCons
          ((hs.reindex (fun _ : Fin 1 => j)).sub (hs.reindex (fun _ : Fin 1 => i)))
        have hh := hasFiniteNashCover_affineBand hg (H 2 B g hg)
          (by intro x hx; exact ne_of_gt (sub_pos.mpr (hlt x hx)))
          (Ioo 0 1) isOpen_Ioo (isConnected_Ioo (by norm_num)) hsIoo
        convert hh using 1
        ext y
        simp only [mem_ofPred_eq,verticalPieceSet,mem_Ioo,g,Fin.cons_zero,Fin.cons_one]
        constructor
        · rintro ⟨hy,hylo,hyhi⟩
          have hd : 0 < f (Fin.tail y) j-f (Fin.tail y) i := sub_pos.mpr (hlt _ hy)
          refine ⟨hy,(y 0-f (Fin.tail y) i)/(f (Fin.tail y) j-f (Fin.tail y) i),
            ⟨div_pos (sub_pos.mpr hylo) hd,(div_lt_one hd).mpr (by linarith)⟩,?_⟩
          field_simp
          ring
        · rintro ⟨hy,t,⟨ht0,ht1⟩,he⟩
          have hd : 0 < f (Fin.tail y) j-f (Fin.tail y) i := sub_pos.mpr (hlt _ hy)
          exact ⟨hy,by nlinarith,by nlinarith⟩

end Release061

end

end OAI
