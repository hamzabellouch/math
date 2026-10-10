import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ComparableBox03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement
end
end

section
noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeLocalHaar
open CubeFaces LeibmanSquare CubeTaylorExpansion CubeHorizontalIrrationality
open RationalLattice MeasureTheory Filter ComparableBoxLeibman MalcevCharacters AbelianMalcevTorus
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n t d v : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
variable (Γ : Subgroup G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H Γ ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) (QuotientGroup.instTopologicalSpace (cubeLattice H Γ)) inferInstance]
variable [mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H Γ))
local instance : TopologicalSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include h01 hs hsk hqbound hq hΓ htop in
 

theorem haar_limit_scaled
    (L : ℕ→ℝ) (hL : Tendsto L atTop atTop)
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(L N)^j)
        atTop atTop)
    (c₀ C₀ : ℝ) (B : NNReal) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B)
    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ) :
    letI : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_compact cc (cubeLattice H Γ) hΓ mtr htop
    letI : BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_borelSpace (cubeLattice H Γ) mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(L N)≤hi i-lo i) →
      (∀ i,-C₀*(L N)≤lo i ∧ hi i≤C₀*(L N)) →
      ∀ F : C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ),
        LipschitzWith B F → ‖F‖≤B →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
          (cubePolynomial c H S hH (a N) s
            (fun i => ((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))))-(∫ y,F y ∂μ)‖<η := by
  let K := CubeMaxFiltration.filtration H (Finset.univ : Finset ι)
  have hK0 : K.level 0=⊤ := CubeMaxFiltration.filtration_zero H Finset.univ
  have hK1 : K.level 1=⊤ := CubeMaxFiltration.filtration_one H Finset.univ h01
  let : ∀ k,(K.level k).Normal := fun k => LeibmanSquare.level_normal K hK0 k
  let φ : (Fin v→ℤ)→+(Option ι→ℝ) :=
    { toFun := fun x i => (x (e i):ℝ)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  let f (N : ℕ) (x : Fin v→ℤ) := cubePolynomial c H S hH (a N) s (φ x)
  have hf (N : ℕ) : LeibmanSquare.Polynomial K 0 (f N) :=
    polynomial_comp K (cubePolynomial_adapted c H S hH (a N) s) φ
  exact haar_limit_fixed_progression_scaled cc hsk K hK0 hK1 s
    (CubeMaxFiltration.filtration_bot H Finset.univ hs) q hqbound hq
    (cubeLattice H Γ) hΓ htop L hL μ v f hf
    (fun χ hn hc hχΓ => grid_irrationality_scaled L c H S hH Γ h01 s hs e a hirr χ hn hc hχΓ)
    c₀ C₀ B hc₀ hC₀ hB d₀ hd₀ r

end CubeLocalHaar
end
end
 
end

section
 

section
noncomputable section
open scoped BigOperators Topology commutatorElement
namespace CubeLocalHaar
open CubeFaces LeibmanSquare CubeTaylorExpansion CubeHorizontalIrrationality
open RationalLattice MeasureTheory Filter ComparableBoxLeibman MalcevCharacters AbelianMalcevTorus
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]
variable {n t d v : ℕ} (c : RealCoordinates G n) (H : Filtration G)
variable (S : ℕ→Set (Fin n))
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i∈S k,c.coord g i=0)
variable (Γ : Subgroup G) (h01 : H.level 0=H.level 1)
variable (s : ℕ) (hs : H.level (s+1)=⊥) (e : Option ι≃Fin v)
variable (cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) (t+d))
variable (hsk : SecondKind cc)
variable (q : ℕ→ℕ) (hqbound : ∀ k,q k ≤ t+d)
variable (hq : ∀ k (g : cube H (Finset.univ : Finset ι) 0),
  g∈(CubeMaxFiltration.filtration H Finset.univ).level k ↔
    ∀ i : Fin (t+d),i.val < q k → cc.coord g i=0)
variable (hΓ : ∀ g : cube H (Finset.univ : Finset ι) 0,
  g∈cubeLattice H Γ ↔ ∀ i,∃ z : ℤ,cc.coord g i=z)
variable [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable [hBorel : @BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) (QuotientGroup.instTopologicalSpace (cubeLattice H Γ)) inferInstance]
variable [mtr : MetricSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace (cubeLattice H Γ))
local instance scaledCompactCubeTopology : TopologicalSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include h01 hs hsk hqbound hq hΓ htop in
 

theorem haar_limit_compact_scaled
    (L : ℕ→ℝ) (hL : Tendsto L atTop atTop)
    (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ))
    [IsProbabilityMeasure μ]
    [SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0) _ μ]
    (a : ℕ→∀ k : ℕ,H.level k)
    (hirr : ∀ j : ℕ,0 < j → j ≤ s → ∀ ξ : H.level j→*Multiplicative ℝ,
      ξ≠1 → Continuous ξ → RationalCharacter Γ ξ →
      (∀ x (hx : x∈H.level (j+1)),ξ ⟨x,H.antitone (Nat.le_succ _) hx⟩=1) →
      (∀ i k : ℕ,0 < i → 0 < k → ∀ h : i+k=j,
        ∀ x (hx : x∈H.level i) y (hy : y∈H.level k),
          ξ ⟨⁅x,y⁆,by rw [←h]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩=1) →
      Tendsto (fun N : ℕ => ‖((ξ (a N j)).toAdd:UnitAddCircle)‖*(L N)^j)
        atTop atTop)
    (c₀ C₀ : ℝ) (hc₀ : 0<c₀) (hC₀ : 0<C₀)
    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ)
    (K : Set C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ))
    (hK : IsCompact K) :
    letI : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_compact cc (cubeLattice H Γ) hΓ mtr htop
    letI : BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
      metric_borelSpace (cubeLattice H Γ) mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(L N)≤hi i-lo i) →
      (∀ i,-C₀*(L N)≤lo i ∧ hi i≤C₀*(L N)) →
      ∀ F : C(((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),ℂ),
        F∈K →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
          (cubePolynomial c H S hH (a N) s
            (fun i => ((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))))-(∫ y,F y ∂μ)‖<η  := by
  let : CompactSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
    metric_compact cc (cubeLattice H Γ) hΓ mtr htop
  let : BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ) :=
    metric_borelSpace (cubeLattice H Γ) mtr htop
  intro η hη
  obtain ⟨δ,hδ,htest⟩ := FiniteHaarTests.compact_tests (κ := Fin v→ℤ) μ K hK η hη
  have hh := haar_limit_scaled c H S hH Γ h01 s hs e cc hsk q hqbound hq hΓ htop L hL μ a hirr
    c₀ C₀ 1 hc₀ hC₀ (by norm_num) d₀ hd₀ r δ hδ
  filter_upwards [hh] with N hN
  intro lo hi hlo hhi F hF
  apply htest (integerBox v lo hi)
    (fun x => QuotientGroup.mk (cubePolynomial c H S hH (a N) s
      (fun i => ((r (e i)+(d₀:ℤ)*x (e i):ℤ):ℝ)))) _ F hF
  intro φ hφ hφn
  exact hN lo hi hlo hhi φ hφ hφn

end CubeLocalHaar
end
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
namespace CubeRationalCharts
open CubeFaces
variable {G ι : Type} [Group G] [DecidableEq ι]

 
theorem cube_corner_mem (H : Filtration G) (I : Finset ι) (k : ℕ)
    {f : Finset ι → G} (hf : f ∈ cube H I k) (Γ : Subgroup G)
    (hv : ∀ v, v ⊂ I → f v ∈ Γ) (hlevel : H.level (I.card + k) ≤ Γ) :
    f I ∈ Γ := by
  induction I using Finset.induction_on generalizing k f with
  | empty =>
      exact hlevel (by simpa using cube_eval_mem H hf ∅)
  | @insert a I ha ih =>
      obtain ⟨l, hl, u, hu, rfl⟩ := cube_decompose H a I k hf
      have hnot (v : Finset ι) (hvI : v ⊆ I) : a ∉ v := fun hav => ha (hvI hav)
      have hlv (v : Finset ι) (hvI : v ⊆ I) : l v ∈ Γ := by
        have hproper : v ⊂ insert a I := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hvI.trans (Finset.subset_insert a I), ?_⟩
          intro he
          exact hnot v hvI (he.symm ▸ Finset.mem_insert_self a I)
        simpa [upper, hnot v hvI] using hv v hproper
      have huv (v : Finset ι) (hvI : v ⊂ I) : u v ∈ Γ := by
        have hproper : insert a v ⊂ insert a I := by
          exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset_insert a hvI.subset,
            fun he => hvI.ne (by simpa [ha, hnot v hvI.subset] using congrArg (fun s => s.erase a) he)⟩
        have hm := hv (insert a v) hproper
        simp only [Pi.mul_apply, upper, MonoidHom.coe_mk, OneHom.coe_mk,
          Finset.mem_insert_self, ite_true] at hm
        rw [cube_insert_irrelevant H ha hl, cube_insert_irrelevant H ha hu] at hm
        exact (Γ.mul_mem_cancel_left (hlv v hvI.subset)).mp hm
      have huI : u I ∈ Γ := ih (k + 1) hu huv (by
        simpa [Finset.card_insert_of_notMem ha, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hlevel)
      simpa [upper, cube_insert_irrelevant H ha hl, cube_insert_irrelevant H ha hu] using
        Γ.mul_mem (hlv I le_rfl) huI

 
def restrict (D : Finset ι) : (Finset ι → G) →* (Finset ι → G) where
  toFun f v := f (v ∩ D)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma restrict_mem (H : Filtration G) {I : Finset ι} {k : ℕ}
    {f : Finset ι → G} (hf : f ∈ cube H I k) (D : Finset ι) :
    restrict D f ∈ cube H D k := by
  have hle : cube H I k ≤ (cube H D k).comap (restrict D) := by
    refine iSup_le fun E => iSup_le fun hE => ?_
    rintro f ⟨g,hg,rfl⟩
    change restrict D (face E g) ∈ cube H D k
    by_cases hED : E ⊆ D
    · have he : restrict D (face E g) = face E g := by
        funext v
        simp [restrict,face_apply,Finset.subset_inter_iff,hED]
      rw [he]
      exact face_mem_cube H hED hg
    · have he : restrict D (face E g) = 1 := by
        funext v
        simp [restrict,face_apply,Finset.subset_inter_iff,hED]
      rw [he]
      exact (cube H D k).one_mem
  exact hle hf

lemma supported_value_mem (H : Filtration G) {I D : Finset ι} {k : ℕ}
    {f : Finset ι → G} (hf : f ∈ cube H I k)
    (hv : ∀ E, E ⊂ D → f E = 1) : f D ∈ H.level (D.card+k) := by
  have hh := cube_corner_mem H D k (restrict_mem H hf D) (H.level (D.card+k))
    (fun E hE => by
      change f (E ∩ D) ∈ H.level (D.card+k)
      rw [Finset.inter_eq_left.mpr hE.subset,hv E hE]
      exact (H.level _).one_mem) le_rfl
  simpa [restrict] using hh

variable {M : ℕ} (e : Fin M ≃ Finset ι)

def Compatible : Prop := ∀ i j : Fin M, e i ⊂ e j → i < j

lemma not_subset_of_lt (he : Compatible e) {i j : Fin M} (hij : i < j) :
    ¬ e j ⊆ e i := by
  intro hji
  by_cases heq : e j = e i
  · have := e.injective heq
    omega
  · have := he j i (Finset.ssubset_iff_subset_ne.mpr ⟨hji,heq⟩)
    omega

 
def residual (f : Finset ι → G) : ℕ → (Finset ι → G)
  | 0 => f
  | j+1 => if h : j < M then
      (face (e ⟨j,h⟩) (residual f j (e ⟨j,h⟩)))⁻¹ * residual f j
    else residual f j

def coefficients (f : Finset ι → G) (i : Fin M) : G := residual e f i.val (e i)

 

def prefixProduct (a : Fin M → G) : ℕ → (Finset ι → G)
  | 0 => 1
  | j+1 => if h : j < M then prefixProduct a j * face (e ⟨j,h⟩) (a ⟨j,h⟩)
    else prefixProduct a j

def assemble (a : Fin M → G) : Finset ι → G := prefixProduct e a M

lemma residual_prior (he : Compatible e) (f : Finset ι → G) (k : ℕ)
    (i : Fin M) (hi : i.val < k) : residual e f k (e i) = 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [residual]
    split_ifs with hk
    · change (face (e ⟨k,hk⟩) (residual e f k (e ⟨k,hk⟩)) (e i))⁻¹ *
        residual e f k (e i) = 1
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hik | hik
      · rw [face_apply,ite_eq_right (not_subset_of_lt e he (show i < ⟨k,hk⟩ from hik)),ih hik]
        simp
      · have heq : (⟨k,hk⟩ : Fin M) = i := Fin.ext hik.symm
        subst heq
        simp [face_apply]
    · exact ih (by omega)

lemma residual_final (he : Compatible e) (f : Finset ι → G) : residual e f M = 1 := by
  funext D
  obtain ⟨i,rfl⟩ := e.surjective D
  exact residual_prior e he f M i i.isLt

lemma prefixProduct_residual (f : Finset ι → G) (k : ℕ) :
    prefixProduct e (coefficients e f) k * residual e f k = f := by
  induction k with
  | zero => simp [prefixProduct,residual]
  | succ k ih =>
    rw [prefixProduct,residual]
    split_ifs with hk
    · simpa only [coefficients,mul_assoc,mul_inv_cancel_left] using ih
    · exact ih

lemma assemble_coefficients (he : Compatible e) (f : Finset ι → G) :
    assemble e (coefficients e f) = f := by
  have hh := prefixProduct_residual e f M
  simpa only [residual_final e he f,mul_one,assemble] using hh

lemma prefixProduct_eval_after (he : Compatible e) (a : Fin M → G) (i : Fin M)
    (k : ℕ) (hik : i.val < k) :
    prefixProduct e a k (e i) = prefixProduct e a (i.val+1) (e i) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hik) with hik' | hik'
    · rw [prefixProduct]
      split_ifs with hk
      · change prefixProduct e a k (e i) * face (e ⟨k,hk⟩) (a ⟨k,hk⟩) (e i) = _
        rw [face_apply,ite_eq_right (not_subset_of_lt e he (show i < ⟨k,hk⟩ from hik')),mul_one]
        exact ih hik'
      · exact ih hik'
    · subst k
      rfl

lemma assemble_eval (he : Compatible e) (a : Fin M → G) (i : Fin M) :
    assemble e a (e i) = prefixProduct e a i.val (e i) * a i := by
  rw [assemble,prefixProduct_eval_after e he a i M i.isLt,prefixProduct,dite_eq_left i.isLt]
  simp [face_apply]

lemma assemble_injective (he : Compatible e) : Function.Injective (assemble (G:=G) e) := by
  intro a b hab
  have hp : ∀ k, prefixProduct e a k = prefixProduct e b k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [prefixProduct,prefixProduct]
      split_ifs with hk
      · have hv := congrFun hab (e ⟨k,hk⟩)
        rw [assemble_eval e he,assemble_eval e he] at hv
        change prefixProduct e a k (e ⟨k,hk⟩) * a ⟨k,hk⟩ =
          prefixProduct e b k (e ⟨k,hk⟩) * b ⟨k,hk⟩ at hv
        rw [ih] at hv
        rw [ih,mul_left_cancel hv]
      · exact ih
  funext i
  have hv := congrFun hab (e i)
  rw [assemble_eval e he,assemble_eval e he,hp i.val] at hv
  exact mul_left_cancel hv

lemma coefficients_assemble (he : Compatible e) (a : Fin M → G) :
    coefficients e (assemble e a) = a :=
  assemble_injective e he (assemble_coefficients e he (assemble e a))

lemma coefficients_mem (he : Compatible e) (H : Filtration G) (I : Finset ι)
    (hI : ∀ D : Finset ι, D ⊆ I) (k : ℕ) {f : Finset ι → G} (hf : f ∈ cube H I k) :
    ∀ i : Fin M, coefficients e f i ∈ H.level ((e i).card+k) := by
  have hr : ∀ j, residual e f j ∈ cube H I k := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [residual]
      split_ifs with hj
      · apply (cube H I k).mul_mem _ ih
        apply (cube H I k).inv_mem
        apply face_mem_cube H (hI _)
        apply supported_value_mem H ih
        intro E hE
        obtain ⟨i,rfl⟩ := e.surjective E
        exact residual_prior e he f j i (he i ⟨j,hj⟩ hE)
      · exact ih
  intro i
  apply supported_value_mem H (hr i.val)
  intro E hE
  obtain ⟨j,rfl⟩ := e.surjective E
  exact residual_prior e he f i.val j (he j i hE)

lemma assemble_mem (H : Filtration G) (I : Finset ι)
    (hI : ∀ D : Finset ι, D ⊆ I) (k : ℕ) (a : Fin M → G)
    (ha : ∀ i, a i ∈ H.level ((e i).card+k)) : assemble e a ∈ cube H I k := by
  have hp : ∀ j, prefixProduct e a j ∈ cube H I k := by
    intro j
    induction j with
    | zero => exact (cube H I k).one_mem
    | succ j ih =>
      rw [prefixProduct]
      split_ifs with hj
      · exact (cube H I k).mul_mem ih (face_mem_cube H (hI _) (ha _))
      · exact ih
  exact hp M

lemma coefficients_lattice (he : Compatible e) (Γ : Subgroup G) (f : Finset ι → G) :
    (∀ D, f D ∈ Γ) ↔ ∀ i, coefficients e f i ∈ Γ := by
  constructor
  · intro hf
    have hr : ∀ k D, residual e f k D ∈ Γ := by
      intro k
      induction k with
      | zero => exact hf
      | succ k ih =>
        intro D
        rw [residual]
        split_ifs with hk
        · apply Γ.mul_mem _ (ih D)
          apply Γ.inv_mem
          simp only [face_apply]
          split_ifs
          · exact ih _
          · exact Γ.one_mem
        · exact ih D
    exact fun i => hr i.val (e i)
  · intro hf
    have hp : ∀ k D, prefixProduct e (coefficients e f) k D ∈ Γ := by
      intro k
      induction k with
      | zero => exact fun _ => Γ.one_mem
      | succ k ih =>
        intro D
        rw [prefixProduct]
        split_ifs with hk
        · apply Γ.mul_mem (ih D)
          simp only [face_apply]
          split_ifs
          · exact hf _
          · exact Γ.one_mem
        · exact ih D
    intro D
    rw [← assemble_coefficients e he f]
    exact hp M D

section Topology
variable [TopologicalSpace G] [IsTopologicalGroup G]

lemma residual_continuous (k : ℕ) : Continuous (fun f : Finset ι → G => residual e f k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    simp only [residual]
    split_ifs with hk
    · exact ((continuous_face _).comp ((continuous_apply _).comp ih)).inv.mul ih
    · exact ih

lemma coefficients_continuous : Continuous (coefficients (G:=G) e) := by
  apply continuous_pi
  intro i
  exact (continuous_apply _).comp (residual_continuous e i.val)

lemma prefixProduct_continuous (k : ℕ) :
    Continuous (fun a : Fin M → G => prefixProduct e a k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    simp only [prefixProduct]
    split_ifs with hk
    · exact ih.mul ((continuous_face _).comp (continuous_apply _))
    · exact ih

lemma assemble_continuous : Continuous (assemble (G:=G) e) := prefixProduct_continuous e M

variable [Fintype ι]

 

def faceHomeomorph (he : Compatible e) (H : Filtration G) (k : ℕ) :
    (∀ i : Fin M, H.level ((e i).card+k)) ≃ₜ cube H (Finset.univ : Finset ι) k where
  toFun a := ⟨assemble e (fun i => (a i).val),
    assemble_mem e H Finset.univ (fun _ => Finset.subset_univ _) k _ (fun i => (a i).property)⟩
  invFun f i := ⟨coefficients e f.val i,
    coefficients_mem e he H Finset.univ (fun _ => Finset.subset_univ _) k f.property i⟩
  left_inv a := by
    funext i
    apply Subtype.ext
    exact congrFun (coefficients_assemble e he (fun i => (a i).val)) i
  right_inv f := by
    apply Subtype.ext
    exact assemble_coefficients e he f.val
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (assemble_continuous e).comp (continuous_pi (fun i =>
      continuous_subtype_val.comp (continuous_apply i)))
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact ((continuous_apply i).comp (coefficients_continuous e)).comp continuous_subtype_val

lemma faceHomeomorph_lattice (he : Compatible e) (H : Filtration G) (k : ℕ)
    (Γ : Subgroup G) (a : ∀ i : Fin M, H.level ((e i).card+k)) :
    (∀ D, (faceHomeomorph e he H k a).val D ∈ Γ) ↔ ∀ i, (a i).val ∈ Γ := by
  rw [coefficients_lattice e he]
  change (∀ i, coefficients e (assemble e (fun i => (a i).val)) i ∈ Γ) ↔ _
  rw [coefficients_assemble e he]

end Topology

 
omit [DecidableEq ι] in
theorem exists_compatible_order [Fintype ι] :
    ∃ e : Fin (Fintype.card (Finset ι)) ≃ Finset ι, Compatible e := by
  classical
  let code := Fintype.equivFin (Finset ι)
  let key : Finset ι → Lex (ℕ × Fin (Fintype.card (Finset ι))) :=
    fun D => toLex (D.card,code D)
  have hi : Function.Injective key := by
    intro D E h
    exact code.injective (congrArg (fun x => (ofLex x).2) h)
  let ord : LinearOrder (Finset ι) := LinearOrder.lift' key hi
  let e := Fintype.orderIsoFinOfCardEq (Finset ι) rfl
  refine ⟨e.toEquiv,?_⟩
  intro i j hij
  apply (@OrderIso.lt_iff_lt _ _ _ ord.toPartialOrder.toPreorder e).mp
  change key (e i) < key (e j)
  exact Prod.Lex.left _ _ (Finset.card_lt_card hij)

section Homomorphisms
variable {K : Type} [Group K]

lemma residual_map (φ : G →* K) (f : Finset ι → G) (k : ℕ) :
    residual e (fun D => φ (f D)) k = fun D => φ (residual e f k D) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [residual,residual]
    split_ifs with hk
    · funext D
      simp only [Pi.mul_apply,Pi.inv_apply,ih,face_apply,map_mul,map_inv]
      split_ifs <;> simp
    · exact ih

lemma coefficients_map (φ : G →* K) (f : Finset ι → G) (i : Fin M) :
    coefficients e (fun D => φ (f D)) i = φ (coefficients e f i) := by
  exact congrFun (residual_map e φ f i.val) (e i)

lemma prefixProduct_map (φ : G →* K) (a : Fin M → G) (k : ℕ) :
    prefixProduct e (fun i => φ (a i)) k = fun D => φ (prefixProduct e a k D) := by
  induction k with
  | zero => ext D; exact φ.map_one.symm
  | succ k ih =>
    rw [prefixProduct,prefixProduct]
    split_ifs with hk
    · funext D
      simp only [Pi.mul_apply,ih,face_apply,map_mul]
      split_ifs <;> simp
    · exact ih

lemma assemble_map (φ : G →* K) (a : Fin M → G) (D : Finset ι) :
    assemble e (fun i => φ (a i)) D = φ (assemble e a D) :=
  congrFun (prefixProduct_map e φ a M) D

lemma coefficients_map_product (φ : G →* K) (a b : Fin M → G) (i : Fin M) :
    φ (coefficients e (assemble e a * assemble e b) i) =
      coefficients e (assemble e (fun j => φ (a j)) * assemble e (fun j => φ (b j))) i := by
  rw [← coefficients_map]
  congr 1
  funext D
  simp only [Pi.mul_apply,map_mul,assemble_map]

end Homomorphisms

section Commutative
variable {K : Type} [CommGroup K]

lemma assemble_mul (a b : Fin M → K) :
    assemble e (a*b) = assemble e a * assemble e b := by
  have hp : ∀ k, prefixProduct e (a*b) k = prefixProduct e a k * prefixProduct e b k := by
    intro k
    induction k with
    | zero => simp [prefixProduct]
    | succ k ih =>
      rw [prefixProduct,prefixProduct,prefixProduct]
      split_ifs with hk
      · funext D
        simp only [Pi.mul_apply,ih,face_apply]
        split_ifs <;> simp [mul_assoc,mul_comm,mul_left_comm]
      · exact ih
  exact hp M

lemma coefficients_mul (he : Compatible e) (f g : Finset ι → K) :
    coefficients e (f*g) = coefficients e f * coefficients e g := by
  calc
    _ = coefficients e (assemble e (coefficients e f) * assemble e (coefficients e g)) := by
      rw [assemble_coefficients e he,assemble_coefficients e he]
    _ = _ := by rw [← assemble_mul,coefficients_assemble e he]

lemma coefficients_hom_product (he : Compatible e) (φ : G →* K)
    (a b : Fin M → G) (i : Fin M) :
    φ (coefficients e (assemble e a * assemble e b) i) = φ (a i)*φ (b i) := by
  rw [coefficients_map_product,coefficients_mul e he,
    coefficients_assemble e he,coefficients_assemble e he]
  rfl
end Commutative

section Triangular
open RationalLattice
variable [TopologicalSpace G] {n : ℕ} (c : RealCoordinates G n)

 
def lowerPairs (i : Fin n) : Subgroup (G × G) where
  carrier := {g | ∀ j : Fin n, j < i → c.coord g.1 j=c.coord g.2 j}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh
    exact mul_lower_congr c i hg hh
  inv_mem' := by
    intro g hg j hj
    have haux : ∀ k (hk : k < i.val),
        c.coord g.1⁻¹ ⟨k,lt_trans hk i.isLt⟩=c.coord g.2⁻¹ ⟨k,lt_trans hk i.isLt⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro hk
        let u : Fin n := ⟨k,lt_trans hk i.isLt⟩
        have hcorr := correction_eq_of_lower_eq c u
          (g:=g.1) (g':=g.2) (h:=g.1⁻¹) (h':=g.2⁻¹)
          (fun j hj => hg j (lt_trans hj hk))
          (fun j hj => ih j.val hj (lt_trans hj hk))
        rw [mul_inv_cancel,mul_inv_cancel,c.one_coord] at hcorr
        have he := hg u hk
        dsimp [u] at he hcorr ⊢
        linarith
    exact haux j.val hj

 

def differenceCharacter (i : Fin n) : lowerPairs c i →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (c.coord g.val.1 i-c.coord g.val.2 i)
  map_one' := by apply Multiplicative.toAdd.injective; simp [c.one_coord]
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change c.coord (g.val.1*h.val.1) i-c.coord (g.val.2*h.val.2) i =
      (c.coord g.val.1 i-c.coord g.val.2 i)+(c.coord h.val.1 i-c.coord h.val.2 i)
    have he := correction_eq_of_lower_eq c i g.property h.property
    linarith

 

theorem cube_mul_correction_lower (he : Compatible e) (i : Fin n)
    (a a' b b' : Fin M → G)
    (ha : ∀ D j, j < i → c.coord (a D) j=c.coord (a' D) j)
    (hb : ∀ D j, j < i → c.coord (b D) j=c.coord (b' D) j) (D : Fin M) :
    c.coord (coefficients e (assemble e a * assemble e b) D) i-
        c.coord (a D) i-c.coord (b D) i =
      c.coord (coefficients e (assemble e a' * assemble e b') D) i-
        c.coord (a' D) i-c.coord (b' D) i := by
  let A : Fin M → lowerPairs c i := fun D => ⟨(a D,a' D),ha D⟩
  let B : Fin M → lowerPairs c i := fun D => ⟨(b D,b' D),hb D⟩
  let fst : lowerPairs c i →* G := (MonoidHom.fst G G).comp (lowerPairs c i).subtype
  let snd : lowerPairs c i →* G := (MonoidHom.snd G G).comp (lowerPairs c i).subtype
  have hfst := coefficients_map_product e fst A B D
  have hsnd := coefficients_map_product e snd A B D
  have hdiff := coefficients_hom_product e he (differenceCharacter c i) A B D
  apply_fun Multiplicative.toAdd at hdiff
  change c.coord (fst (coefficients e (assemble e A * assemble e B) D)) i-
      c.coord (snd (coefficients e (assemble e A * assemble e B) D)) i =
    (c.coord (a D) i-c.coord (a' D) i)+(c.coord (b D) i-c.coord (b' D) i) at hdiff
  change fst (coefficients e (assemble e A * assemble e B) D) =
    coefficients e (assemble e a * assemble e b) D at hfst
  change snd (coefficients e (assemble e A * assemble e B) D) =
    coefficients e (assemble e a' * assemble e b') D at hsnd
  rw [hfst,hsnd] at hdiff
  linarith

end Triangular

section Polynomial
open RationalLattice RationalPolynomialMap
variable [TopologicalSpace G] {n : ℕ} (c : RealCoordinates G n) {σ : Type*}

lemma residual_polynomial {F : (σ → ℝ) → (Finset ι → G)}
    (hF : ∀ D, IsPolynomialMap c (fun x => F x D)) (k : ℕ) :
    ∀ D, IsPolynomialMap c (fun x => residual e (F x) k D) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    intro D
    by_cases hk : k < M
    · by_cases hD : e ⟨k,hk⟩ ⊆ D
      · simpa only [residual,dite_eq_left hk,Pi.mul_apply,Pi.inv_apply,face_apply,ite_eq_left hD] using
          polynomialMap_mul c (polynomialMap_inv c (ih (e ⟨k,hk⟩))) (ih D)
      · simpa only [residual,dite_eq_left hk,Pi.mul_apply,Pi.inv_apply,face_apply,ite_eq_right hD,
          inv_one,one_mul] using ih D
    · simpa only [residual,dite_eq_right hk] using ih D

lemma coefficients_polynomial {F : (σ → ℝ) → (Finset ι → G)}
    (hF : ∀ D, IsPolynomialMap c (fun x => F x D)) (i : Fin M) :
    IsPolynomialMap c (fun x => coefficients e (F x) i) :=
  residual_polynomial e c hF i.val (e i)

lemma prefixProduct_polynomial {A : (σ → ℝ) → (Fin M → G)}
    (hA : ∀ i, IsPolynomialMap c (fun x => A x i)) (k : ℕ) :
    ∀ D, IsPolynomialMap c (fun x => prefixProduct e (A x) k D) := by
  induction k with
  | zero => exact fun _ => polynomialMap_one c
  | succ k ih =>
    intro D
    by_cases hk : k < M
    · by_cases hD : e ⟨k,hk⟩ ⊆ D
      · simpa only [prefixProduct,dite_eq_left hk,Pi.mul_apply,face_apply,ite_eq_left hD] using
          polynomialMap_mul c (ih D) (hA ⟨k,hk⟩)
      · simpa only [prefixProduct,dite_eq_left hk,Pi.mul_apply,face_apply,ite_eq_right hD,mul_one] using ih D
    · simpa only [prefixProduct,dite_eq_right hk] using ih D

lemma assemble_polynomial {A : (σ → ℝ) → (Fin M → G)}
    (hA : ∀ i, IsPolynomialMap c (fun x => A x i)) (D : Finset ι) :
    IsPolynomialMap c (fun x => assemble e (A x) D) :=
  prefixProduct_polynomial e c hA M D
end Polynomial

 
abbrev FreeIndex (n : ℕ) (q : ℕ → ℕ) (k : ℕ) :=
  {p : Fin M × Fin n // q ((e p.1).card+k) ≤ p.2.val}

section FreeCoordinates
open RationalLattice RationalPolynomialMap
variable [TopologicalSpace G] {n : ℕ} (c : RealCoordinates G n)
variable (q : ℕ → ℕ) (k : ℕ)

def expand (x : FreeIndex e n q k → ℝ) (D : Fin M) : G :=
  c.coord.symm (fun j => if h : q ((e D).card+k) ≤ j.val then x ⟨(D,j),h⟩ else 0)

omit [DecidableEq ι] in
@[simp] lemma expand_coord (x : FreeIndex e n q k → ℝ) (D : Fin M) (j : Fin n) :
    c.coord (expand e c q k x D) j =
      if h : q ((e D).card+k) ≤ j.val then x ⟨(D,j),h⟩ else 0 := by
  simp only [expand,Homeomorph.apply_symm_apply]

omit [DecidableEq ι] in
lemma expand_polynomial (D : Fin M) :
    IsPolynomialMap c (fun x : FreeIndex e n q k → ℝ => expand e c q k x D) := by
  intro j
  simp only [expand_coord]
  split_ifs
  · exact coordinate _
  · exact zero

omit [DecidableEq ι] in
lemma expand_continuous : Continuous (expand e c q k) := by
  apply continuous_pi
  intro D
  apply c.coord.symm.continuous.comp
  apply continuous_pi
  intro j
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

variable (H : Filtration G)
variable (hq : ∀ d (g : G), g ∈ H.level d ↔ ∀ j : Fin n, j.val < q d → c.coord g j=0)

include hq in
omit [DecidableEq ι] in
lemma expand_mem (x : FreeIndex e n q k → ℝ) (D : Fin M) :
    expand e c q k x D ∈ H.level ((e D).card+k) := by
  apply (hq _ _).mpr
  intro j hj
  simp only [expand_coord,dite_eq_right (not_le_of_gt hj)]

variable [IsTopologicalGroup G] [Fintype ι] (he : Compatible e)

 
def freeHomeomorph : cube H (Finset.univ : Finset ι) k ≃ₜ (FreeIndex e n q k → ℝ) where
  toFun f u := c.coord (coefficients e f.val u.val.1) u.val.2
  invFun x := ⟨assemble e (expand e c q k x),
    assemble_mem e H Finset.univ (fun _ => Finset.subset_univ _) k _
      (expand_mem e c q k H hq x)⟩
  left_inv f := by
    apply Subtype.ext
    have hexp : expand e c q k (fun u => c.coord (coefficients e f.val u.val.1) u.val.2) =
        coefficients e f.val := by
      funext D
      apply c.coord.injective
      funext j
      rw [expand_coord]
      split_ifs with hj
      · rfl
      · have hm := coefficients_mem e he H Finset.univ (fun _ => Finset.subset_univ _) k f.property D
        exact ((hq _ _).mp hm j (Nat.lt_of_not_ge hj)).symm
    change assemble e (expand e c q k (fun u => c.coord (coefficients e f.val u.val.1) u.val.2)) = f.val
    rw [hexp,assemble_coefficients e he]
  right_inv x := by
    funext u
    change c.coord (coefficients e (assemble e (expand e c q k x)) u.val.1) u.val.2 = x u
    rw [coefficients_assemble e he,expand_coord,dite_eq_left u.property]
  continuous_toFun := by
    apply continuous_pi
    intro u
    exact (continuous_apply u.val.2).comp (c.coord.continuous.comp
      ((continuous_apply u.val.1).comp ((coefficients_continuous e).comp continuous_subtype_val)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (assemble_continuous e).comp (expand_continuous e c q k)

lemma freeHomeomorph_apply (f : cube H (Finset.univ : Finset ι) k) (u : FreeIndex e n q k) :
    freeHomeomorph e c q k H hq he f u = c.coord (coefficients e f.val u.val.1) u.val.2 := rfl

lemma expand_freeHomeomorph (f : cube H (Finset.univ : Finset ι) k) :
    expand e c q k (freeHomeomorph e c q k H hq he f) = coefficients e f.val := by
  funext D
  apply c.coord.injective
  funext j
  rw [expand_coord]
  split_ifs with hj
  · rfl
  · have hm := coefficients_mem e he H Finset.univ (fun _ => Finset.subset_univ _) k f.property D
    exact ((hq _ _).mp hm j (Nat.lt_of_not_ge hj)).symm

lemma freeHomeomorph_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j=z)
    (f : cube H (Finset.univ : Finset ι) k) :
    (∀ D, f.val D ∈ Γ) ↔ ∀ u, ∃ z : ℤ, freeHomeomorph e c q k H hq he f u=z := by
  rw [coefficients_lattice e he]
  simp_rw [hΓ]
  constructor
  · intro hf u
    exact hf u.val.1 u.val.2
  · intro hf D j
    by_cases hj : q ((e D).card+k) ≤ j.val
    · exact hf ⟨(D,j),hj⟩
    · refine ⟨0,?_⟩
      have hm := coefficients_mem e he H Finset.univ (fun _ => Finset.subset_univ _) k f.property D
      simpa using (hq _ _).mp hm j (Nat.lt_of_not_ge hj)

end FreeCoordinates

section RankedCoordinates
open RationalLattice RationalPolynomialMap
variable [TopologicalSpace G] {n : ℕ} (c : RealCoordinates G n)
variable (q : ℕ → ℕ) (k : ℕ)

 
def BaseFirst {N : ℕ} (r : Fin N ≃ FreeIndex e n q k) : Prop :=
  ∀ i j, (r i).val.2 < (r j).val.2 → i < j

omit [DecidableEq ι] in
theorem exists_baseFirst_order :
    ∃ r : Fin (Fintype.card (FreeIndex e n q k)) ≃ FreeIndex e n q k,
      BaseFirst e q k r := by
  classical
  let key : FreeIndex e n q k → Lex (Fin n × Fin M) := fun u => toLex (u.val.2,u.val.1)
  have hi : Function.Injective key := by
    intro u v h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x => (ofLex x).2) h
    · exact congrArg (fun x => (ofLex x).1) h
  let ord : LinearOrder (FreeIndex e n q k) := LinearOrder.lift' key hi
  let r := Fintype.orderIsoFinOfCardEq (FreeIndex e n q k) rfl
  refine ⟨r.toEquiv,?_⟩
  intro i j hij
  apply (@OrderIso.lt_iff_lt _ _ _ ord.toPartialOrder.toPreorder r).mp
  change key (r i) < key (r j)
  exact Prod.Lex.left _ _ hij

variable {N : ℕ} (r : Fin N ≃ FreeIndex e n q k)

def truncate (i : Fin N) (x : Fin i.val → ℝ) (u : FreeIndex e n q k) : ℝ :=
  if h : r.symm u < i then x ⟨(r.symm u).val,h⟩ else 0

omit [DecidableEq ι] in
lemma truncate_polynomial (i : Fin N) (u : FreeIndex e n q k) :
    IsPolynomial (fun x : Fin i.val → ℝ => truncate e q k r i x u) := by
  unfold truncate
  split_ifs
  · exact coordinate _
  · exact zero

omit [DecidableEq ι] in
lemma expand_truncate_lower (hr : BaseFirst e q k r) (i : Fin N)
    (x : FreeIndex e n q k → ℝ) (D : Fin M) (j : Fin n) (hj : j < (r i).val.2) :
    c.coord (expand e c q k x D) j =
      c.coord (expand e c q k (truncate e q k r i
        (fun t => x (r ⟨t.val,lt_trans t.isLt i.isLt⟩))) D) j := by
  simp only [expand_coord]
  split_ifs with hqj
  · have hlt : r.symm ⟨(D,j),hqj⟩ < i := by
      apply hr
      rw [r.apply_symm_apply]
      exact hj
    simp only [truncate,dite_eq_left hlt]
    congr 1
    exact (r.apply_symm_apply ⟨(D,j),hqj⟩).symm
  · rfl

variable (H : Filtration G)
variable (hq : ∀ d (g : G), g ∈ H.level d ↔ ∀ j : Fin n, j.val < q d → c.coord g j=0)
variable [IsTopologicalGroup G] [Fintype ι] (he : Compatible e)

def rankedHomeomorph : cube H (Finset.univ : Finset ι) k ≃ₜ (Fin N → ℝ) :=
  (freeHomeomorph e c q k H hq he).trans (Homeomorph.piCongrLeft r).symm

@[simp] lemma rankedHomeomorph_apply (f : cube H (Finset.univ : Finset ι) k) (i : Fin N) :
    rankedHomeomorph e c q k r H hq he f i = c.coord (coefficients e f.val (r i).val.1) (r i).val.2 := rfl

 
def correctionFunction (i : Fin N) (x : Fin i.val ⊕ Fin i.val → ℝ) : ℝ :=
  let A := expand e c q k (truncate e q k r i (fun j => x (.inl j)))
  let B := expand e c q k (truncate e q k r i (fun j => x (.inr j)))
  c.coord (coefficients e (assemble e A * assemble e B) (r i).val.1) (r i).val.2 -
    c.coord (A (r i).val.1) (r i).val.2 - c.coord (B (r i).val.1) (r i).val.2

omit [IsTopologicalGroup G] [Fintype ι] in
lemma correctionFunction_polynomial (i : Fin N) :
    IsPolynomial (correctionFunction e c q k r i) := by
  have hA (D : Fin M) : IsPolynomialMap c (fun x : Fin i.val ⊕ Fin i.val → ℝ =>
      expand e c q k (truncate e q k r i (fun j => x (.inl j))) D) := by
    apply polynomialMap_comp c (expand_polynomial e c q k D)
    intro u
    unfold truncate
    split_ifs
    · exact coordinate _
    · exact zero
  have hB (D : Fin M) : IsPolynomialMap c (fun x : Fin i.val ⊕ Fin i.val → ℝ =>
      expand e c q k (truncate e q k r i (fun j => x (.inr j))) D) := by
    apply polynomialMap_comp c (expand_polynomial e c q k D)
    intro u
    unfold truncate
    split_ifs
    · exact coordinate _
    · exact zero
  exact sub (sub (coefficients_polynomial e c
    (fun D => polynomialMap_mul c (assemble_polynomial e c hA D)
      (assemble_polynomial e c hB D)) (r i).val.1 (r i).val.2)
    (hA (r i).val.1 (r i).val.2)) (hB (r i).val.1 (r i).val.2)

lemma ranked_mul_correction (hr : BaseFirst e q k r)
    (f g : cube H (Finset.univ : Finset ι) k) (i : Fin N) :
    rankedHomeomorph e c q k r H hq he (f*g) i =
      rankedHomeomorph e c q k r H hq he f i + rankedHomeomorph e c q k r H hq he g i +
        correctionFunction e c q k r i (Sum.elim
          (fun j => rankedHomeomorph e c q k r H hq he f ⟨j.val,lt_trans j.isLt i.isLt⟩)
          (fun j => rankedHomeomorph e c q k r H hq he g ⟨j.val,lt_trans j.isLt i.isLt⟩)) := by
  let x := freeHomeomorph e c q k H hq he f
  let y := freeHomeomorph e c q k H hq he g
  have hx : expand e c q k x = coefficients e f.val := expand_freeHomeomorph e c q k H hq he f
  have hy : expand e c q k y = coefficients e g.val := expand_freeHomeomorph e c q k H hq he g
  have h := cube_mul_correction_lower e c he (r i).val.2
    (expand e c q k x) (expand e c q k (truncate e q k r i (fun j => x (r ⟨j.val,lt_trans j.isLt i.isLt⟩))))
    (expand e c q k y) (expand e c q k (truncate e q k r i (fun j => y (r ⟨j.val,lt_trans j.isLt i.isLt⟩))))
    (expand_truncate_lower e c q k r hr i x) (expand_truncate_lower e c q k r hr i y) (r i).val.1
  rw [hx,hy,assemble_coefficients e he,assemble_coefficients e he] at h
  change c.coord (coefficients e (f.val*g.val) (r i).val.1) (r i).val.2 -
      c.coord (coefficients e f.val (r i).val.1) (r i).val.2 -
      c.coord (coefficients e g.val (r i).val.1) (r i).val.2 =
    correctionFunction e c q k r i (Sum.elim
      (fun j => rankedHomeomorph e c q k r H hq he f ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => rankedHomeomorph e c q k r H hq he g ⟨j.val,lt_trans j.isLt i.isLt⟩)) at h
  simp only [rankedHomeomorph_apply] at h ⊢
  change c.coord (coefficients e (f.val*g.val) (r i).val.1) (r i).val.2 = _
  linarith

 
def realCoordinates (hr : BaseFirst e q k r) : RealCoordinates (cube H (Finset.univ : Finset ι) k) N where
  coord := rankedHomeomorph e c q k r H hq he
  one_coord i := by
    rw [rankedHomeomorph_apply]
    have hres (j : ℕ) : residual e (1 : Finset ι → G) j=1 := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [residual]
        split_ifs <;> simp [ih]
    have hone : coefficients e (1 : Finset ι → G) = 1 := by
      funext i
      simp [coefficients,hres]
    simp only [OneMemClass.coe_one,hone,Pi.one_apply,c.one_coord]
  correction i := (correctionFunction_polynomial e c q k r i).choose
  mul_coord f g i := by
    rw [ranked_mul_correction e c q k r H hq he hr]
    congr 1
    exact (correctionFunction_polynomial e c q k r i).choose_spec _

lemma realCoordinates_lattice (hr : BaseFirst e q k r) (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j=z)
    (f : cube H (Finset.univ : Finset ι) k) :
    (∀ D, f.val D ∈ Γ) ↔ ∀ i, ∃ z : ℤ, (realCoordinates e c q k r H hq he hr).coord f i=z := by
  rw [freeHomeomorph_lattice e c q k H hq he Γ hΓ]
  constructor
  · intro hf i
    exact hf (r i)
  · intro hf u
    simpa only [realCoordinates,rankedHomeomorph_apply,freeHomeomorph_apply,r.apply_symm_apply] using hf (r.symm u)

end RankedCoordinates

section AdaptedCubeChart
open RationalLattice MalcevCharacters
variable [TopologicalSpace G] [IsTopologicalGroup G] [Fintype ι]
variable {n : ℕ} (c : RealCoordinates G n) (q : ℕ → ℕ)
variable (H : Filtration G)
variable (hq : ∀ d (g : G), g ∈ H.level d ↔ ∀ j : Fin n, j.val < q d → c.coord g j=0)
variable (he : Compatible e)

include he in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma cube_mem_iff_coefficients (J : Filtration G) (k : ℕ) (f : Finset ι → G) :
    f ∈ cube J (Finset.univ : Finset ι) k ↔ ∀ D, coefficients e f D∈J.level ((e D).card+k) := by
  constructor
  · exact fun hf => coefficients_mem e he J Finset.univ (fun _ => Finset.subset_univ _) k hf
  · intro hf
    rw [← assemble_coefficients e he f]
    exact assemble_mem e J Finset.univ (fun _ => Finset.subset_univ _) k _ hf

variable {N : ℕ} (r : Fin N ≃ FreeIndex e n q 0) (hr : BaseFirst e q 0 r)

lemma realCoordinates_max_level (l : ℕ) (f : cube H (Finset.univ : Finset ι) 0) :
    f ∈ (CubeMaxFiltration.filtration H Finset.univ).level l ↔
      ∀ i : Fin N, (r i).val.2.val < q (max l (e (r i).val.1).card) →
        (realCoordinates e c q 0 r H hq he hr).coord f i=0 := by
  change f.val ∈ CubeMaxFiltration.level H Finset.univ l ↔ _
  rw [CubeMaxFiltration.level_eq_clamp_cube,cube_mem_iff_coefficients e he]
  simp only [CubeMaxFiltration.clamp,Nat.add_zero,hq]
  constructor
  · intro hf i hi
    exact hf (r i).val.1 (r i).val.2 hi
  · intro hf D j hj
    by_cases hfree : q ((e D).card+0) ≤ j.val
    · simpa only [realCoordinates,rankedHomeomorph_apply,r.apply_symm_apply] using
        hf (r.symm ⟨(D,j),hfree⟩) (by simpa only [r.apply_symm_apply] using hj)
    · have hm := coefficients_mem e he H Finset.univ (fun _ => Finset.subset_univ _) 0 f.property D
      exact (hq _ _).mp hm j (Nat.lt_of_not_ge hfree)

include hq he in
 

theorem exists_adapted_cube_coordinates
    (h01 : H.level 0=H.level 1) (s : ℕ) (hs : H.level (s+1)=⊥)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j=z) :
    ∃ N : ℕ, ∃ cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) N,
      SecondKind cc ∧
      (∀ f : cube H (Finset.univ : Finset ι) 0,
        f ∈ CubeLocalHaar.cubeLattice H Γ ↔ ∀ i, ∃ z : ℤ, cc.coord f i=z) ∧
      ∀ l : ℕ, ∃ t : ℕ, t ≤ N ∧ ∀ f : cube H (Finset.univ : Finset ι) 0,
        f ∈ (CubeMaxFiltration.filtration H Finset.univ).level l ↔
          ∀ i : Fin N, i.val < t → cc.coord f i=0 := by
  obtain ⟨r,hr⟩ := exists_baseFirst_order e (n:=n) q 0
  let d := realCoordinates e c q 0 r H hq he hr
  have hdΓ : ∀ f : cube H (Finset.univ : Finset ι) 0,
      f ∈ CubeLocalHaar.cubeLattice H Γ ↔ ∀ i, ∃ z : ℤ, d.coord f i=z :=
    realCoordinates_lattice e c q 0 r H hq he hr Γ hΓ
  have hdH : ∀ l, ∃ I : Set (Fin (Fintype.card (FreeIndex e n q 0))),
      ∀ f : cube H (Finset.univ : Finset ι) 0,
        f ∈ (CubeMaxFiltration.filtration H Finset.univ).level l ↔
          ∀ i ∈ I, d.coord f i=0 := by
    intro l
    exact ⟨{i | (r i).val.2.val < q (max l (e (r i).val.1).card)},
      realCoordinates_max_level e c q H hq he r hr l⟩
  obtain ⟨cc,hcc,hcΓ,hcH⟩ := MalcevWeightedCoordinates.exists_adapted_secondKind_coordinates d
    (CubeMaxFiltration.filtration H Finset.univ) (CubeMaxFiltration.filtration_zero H Finset.univ)
    (CubeMaxFiltration.filtration_one H Finset.univ h01) s
    (CubeMaxFiltration.filtration_bot H Finset.univ hs) hdH
    (CubeLocalHaar.cubeLattice H Γ) hdΓ
  exact ⟨_,cc,hcc,hcΓ,hcH⟩

include hq in
 
theorem cube_chart_from_base
    (h01 : H.level 0=H.level 1) (s : ℕ) (hs : H.level (s+1)=⊥)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ j, ∃ z : ℤ, c.coord g j=z) :
    ∃ N : ℕ, ∃ cc : RealCoordinates (cube H (Finset.univ : Finset ι) 0) N,
      SecondKind cc ∧
      (∀ f : cube H (Finset.univ : Finset ι) 0,
        f ∈ CubeLocalHaar.cubeLattice H Γ ↔ ∀ i, ∃ z : ℤ, cc.coord f i=z) ∧
      ∀ l : ℕ, ∃ t : ℕ, t ≤ N ∧ ∀ f : cube H (Finset.univ : Finset ι) 0,
        f ∈ (CubeMaxFiltration.filtration H Finset.univ).level l ↔
          ∀ i : Fin N, i.val < t → cc.coord f i=0 := by
  obtain ⟨e,he⟩ := exists_compatible_order (ι:=ι)
  exact exists_adapted_cube_coordinates e c q H hq he h01 s hs Γ hΓ

end AdaptedCubeChart

end CubeRationalCharts

end
end

end OAI
