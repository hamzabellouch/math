import OAI.Probability.RadialTransition.ClusterEmbedding

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

def CoreFree {ι : Type uIndex} (t : ℝ) (x : ι → Position) : Prop :=
  ∀ i j, i ≠ j → dist (x i) (x j) < 1 →
    microLength t ≤ dist (x i) (x j) ∧
      dist (x i) (x j) ≤ (1+(1:ℝ)/1000)*microLength t

lemma same_cell_dist_lt {x y : Position} (h : cellOf x = cellOf y) : dist x y < 1 := by
  have hc (k : Fin 3) : |x k-y k| ≤ 1/4 := by
    have hh : ⌊4*x k⌋ = ⌊4*y k⌋ := congrFun h k
    have hxl := Int.floor_le (4*x k)
    have hxu := Int.lt_floor_add_one (4*x k)
    have hyl := Int.floor_le (4*y k)
    have hyu := Int.lt_floor_add_one (4*y k)
    rw [← hh] at hyl hyu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : dist x y ^ 2 ≤ 3*(1/4:ℝ)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ k : Fin 3, (1/4:ℝ)^2 := Finset.sum_le_sum (fun k _ => by
        simpa only [Real.dist_eq] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hc k))
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

lemma CoreFree.dist_bound {ι : Type uIndex} {t : ℝ} {x : ι → Position} (hx : CoreFree t x)
    (i j : ι) (hij : dist (x i) (x j) < 1) :
    dist (x i) (x j) ≤ (1+(1:ℝ)/1000)*microLength t := by
  by_cases he : i = j
  · subst j; simp only [dist_self]; exact mul_nonneg (by norm_num) (microLength_pos t).le
  · exact (hx i j he hij).2

def coreFreeSetoid {ι : Type uIndex} {t : ℝ} {x : ι → Position} (hx : CoreFree t x)
    (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1) : Setoid ι where
  r i j := dist (x i) (x j) < 1
  iseqv := ⟨fun _ => by simp, fun h => by simpa only [dist_comm] using h, by
    intro i j k hij hjk
    have h1 := hx.dist_bound i j hij
    have h2 := hx.dist_bound j k hjk
    linarith [dist_triangle (x i) (x j) (x k)]⟩

lemma coreFree_fiber_card {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    {t : ℝ} {x : ι → Position} (hx : CoreFree t x)
    (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (q : Quotient (coreFreeSetoid hx ht)) :
    (Finset.univ.filter (fun i => Quotient.mk (coreFreeSetoid hx ht) i = q)).card ≤ 4 := by
  classical
  let S := Finset.univ.filter (fun i => Quotient.mk (coreFreeSetoid hx ht) i = q)
  have hclique : (shellGraph x (microLength t)).IsClique S := by
    intro i hi j hj hij
    have hiq : Quotient.mk (coreFreeSetoid hx ht) i = q := (Finset.mem_filter.mp hi).2
    have hjq : Quotient.mk (coreFreeSetoid hx ht) j = q := (Finset.mem_filter.mp hj).2
    exact ⟨hij, hx i j hij (Quotient.exact (hiq.trans hjq.symm))⟩
  by_contra hc
  change ¬ S.card ≤ 4 at hc
  have h5 : 5 ≤ S.card := by omega
  exact (SimpleGraph.CliqueFree.mono h5 (shellGraph_cliqueFree x (microLength_pos t))) S
    ⟨hclique, rfl⟩

lemma coreFree_roots {ι : Type uIndex} [Fintype ι] {t L : ℝ} {x : ι → Position}
    (hx : CoreFree t x) (ht : 2*((1+(1:ℝ)/1000)*microLength t) < 1)
    (hbox : ∀ i, x i ∈ cube L) :
    Fintype.card (Quotient (coreFreeSetoid hx ht)) ≤ packingNumber L ∧
      Function.Injective (fun q : Quotient (coreFreeSetoid hx ht) => cellOf (x q.out)) := by
  classical
  let Q := Quotient (coreFreeSetoid hx ht)
  have hsep (q r : Q) (hqr : q ≠ r) : 1 ≤ dist (x q.out) (x r.out) := by
    by_contra! hh
    apply hqr
    have he : Quotient.mk (coreFreeSetoid hx ht) q.out = Quotient.mk (coreFreeSetoid hx ht) r.out :=
      Quotient.sound hh
    simpa only [Quotient.out_eq] using he
  have hinj : Function.Injective (fun q : Q => x q.out) := by
    intro q r he
    by_contra hne
    have hh := hsep q r hne
    change x q.out = x r.out at he
    rw [he, dist_self] at hh
    norm_num at hh
  constructor
  · let S := Finset.univ.image (fun q : Q => x q.out)
    have hp : IsPacking L S := by
      constructor
      · intro y hy
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
        exact hbox _
      · intro y hy z hz hyz
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hz
        exact hsep q r (fun he => hyz (congrArg (fun q : Q => x q.out) he))
    have hh := packing_card_le hp
    simpa only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ] using hh
  · intro q r he
    by_contra hne
    exact (not_lt_of_ge (hsep q r hne)) (same_cell_dist_lt he)

end RadialTransition
end

end OAI
