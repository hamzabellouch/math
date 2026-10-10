import OAI.Dynamics.SmoothObstruction.EndpointMass

namespace OAI

section

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability Filter Topology
open scoped ContDiff
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
lemma GoodEndpoint.mono {r s : ℕ} {δ ε : ℝ}
    {b : OrthonormalBasis (Fin d) ℝ E} {a : powersetCard (Fin d) r}
    {u : Fin r → E} {v : Fin s → E} {f : E → E} {x : E}
    {D₀ : Matrix (Fin r) (Fin r) ℝ} (h : GoodEndpoint δ b a u v f x D₀) (hδε : δ≤ε) :
    GoodEndpoint ε b a u v f x D₀ :=
  ⟨h.1,h.2.1,h.2.2.1,fun i j => (h.2.2.2 i j).trans hδε⟩

/-- A single endpoint minor tolerance for every possible rank in dimension d. -/
theorem four_endpoint_branch_uniform : ∃ δ : ℝ,0<δ ∧
    ∀ {p q : ℕ},p≤d → q≤d →
    ∀ (U V : Submodule ℝ E) (_ : IsCompl U V)
      (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
      (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E)
      (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
      (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
      (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ x A₀ →
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ z A₀ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ y A₁ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ w A₁ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ x D₀ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ w D₀ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ y D₁ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ z D₁ →
      coordinates b₀ r₀ (f₀ z)=coordinates b₀ r₀ (f₀ x) →
      coordinates b₁ r₁ (f₁ w)=coordinates b₁ r₁ (f₁ y) →
      coordinates c₀ s₀ (g₀ w)=coordinates c₀ s₀ (g₀ x) →
      coordinates c₁ s₁ (g₁ z)=coordinates c₁ s₁ (g₁ y) →
      ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
        (81/121:ℝ)≤|(fderiv ℝ Φ (x,y)).det| ∧
        |(fderiv ℝ Φ (x,y)).det|≤(121/81:ℝ) ∧
        ∀ᶠ t in 𝓝 (x,y),
          coordinates b₀ r₀ (f₀ (Φ t).1)=coordinates b₀ r₀ (f₀ t.1) ∧
          coordinates b₁ r₁ (f₁ (Φ t).2)=coordinates b₁ r₁ (f₁ t.2) ∧
          coordinates c₀ s₀ (g₀ (Φ t).2)=coordinates c₀ s₀ (g₀ t.1) ∧
          coordinates c₁ s₁ (g₁ (Φ t).1)=coordinates c₁ s₁ (g₁ t.2) := by
  classical
  have hex (z : Fin (d+1)×Fin (d+1)) := four_endpoint_branch (d:=d) (p:=z.1.val) (q:=z.2.val)
  choose δ hδ hbranch using hex
  obtain ⟨β,hβ,hβδ⟩ := SmoothObstruction.finite_positive_bound δ hδ
  refine ⟨β,hβ,?_⟩
  intro p q hp hq U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ x y z w A₀ A₁ D₀ D₁
    hxF hzF hyF hwF hxP hwP hyP hzP heF heF' heP heP'
  let j : Fin (d+1)×Fin (d+1) := (⟨p,by omega⟩,⟨q,by omega⟩)
  exact hbranch j U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ x y z w A₀ A₁ D₀ D₁
    (hxF.mono (hβδ j)) (hzF.mono (hβδ j)) (hyF.mono (hβδ j)) (hwF.mono (hβδ j))
    (hxP.mono (hβδ j)) (hwP.mono (hβδ j)) (hyP.mono (hβδ j)) (hzP.mono (hβδ j)) heF heF' heP heP'
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The authentic eight endpoint minors give the local Jacobian germ of the
ORIGINAL measurable switch. Rank-zero blocks are included. The agreement is
relative to retained original inputs, not an extension or a different law. -/
theorem controlled_original_germ_uniform (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0<r ∧ 1≤C ∧ 0<β ∧
      ∀ {p q : ℕ},p≤d → q≤d →
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ≤r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        let Z := (extChartAt I a₀) z
        let W := (extChartAt I a₀) w
        let f₀ := extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I a₀).symm
        let f₁ := extChartAt I (a (c (S^[n] y))) ∘ S^[n] ∘ (extChartAt I a₀).symm
        let g₀ := extChartAt I (a (c (S.symm^[n] x))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm
        let g₁ := extChartAt I (a (c (S.symm^[n] y))) ∘ S.symm^[n] ∘ (extChartAt I a₀).symm
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
          (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E₀)
          (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
          (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
          (∀ j∈r₀,b₀ j∈Wf (P x,P (S^[n] x))) →
          (∀ v∈Wf (P x,P (S^[n] x)),∀ j∉r₀,b₀.repr v j=0) →
          (∀ j∈r₁,b₁ j∈Wf (P y,P (S^[n] y))) →
          (∀ v∈Wf (P y,P (S^[n] y)),∀ j∉r₁,b₁.repr v j=0) →
          (∀ j∈s₀,c₀ j∈Wb (P x,P (S.symm^[n] x))) →
          (∀ v∈Wb (P x,P (S.symm^[n] x)),∀ j∉s₀,c₀.repr v j=0) →
          (∀ j∈s₁,c₁ j∈Wb (P y,P (S.symm^[n] y))) →
          (∀ v∈Wb (P y,P (S.symm^[n] y)),∀ j∉s₁,c₁.repr v j=0) →
          GoodEndpoint β b₀ r₀ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₀ X A₀ →
          GoodEndpoint β b₀ r₀ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₀ Z A₀ →
          GoodEndpoint β b₁ r₁ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₁ Y A₁ →
          GoodEndpoint β b₁ r₁ (fun i => (u i:E₀)) (fun i => (v i:E₀)) f₁ W A₁ →
          GoodEndpoint β c₀ s₀ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₀ X D₀ →
          GoodEndpoint β c₀ s₀ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₀ W D₀ →
          GoodEndpoint β c₁ s₁ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₁ Y D₁ →
          GoodEndpoint β c₁ s₁ (fun i => (v i:E₀)) (fun i => (u i:E₀)) g₁ Z D₁ →
          coordinates b₀ r₀ (f₀ Z)=coordinates b₀ r₀ (f₀ X) →
          coordinates b₁ r₁ (f₁ W)=coordinates b₁ r₁ (f₁ Y) →
          coordinates c₀ s₀ (g₀ W)=coordinates c₀ s₀ (g₀ X) →
          coordinates c₁ s₁ (g₁ Z)=coordinates c₁ s₁ (g₁ Y) →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  obtain ⟨r,C,hr,hC,hgerm⟩ := original_pair_germ I hclosed a K hK hKU
  obtain ⟨β,hβ,hbranch⟩ := four_endpoint_branch_uniform (d:=d)
  refine ⟨r,C,β,hr,hC,hβ,?_⟩
  intro p q hp hq A J S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    z w ht1 ht2 ht3 ht4 a₀ X Y Z W f₀ f₁ g₀ g₁ U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ A₀ A₁ D₀ D₁
    hb₀ hz₀ hb₁ hz₁ hc₀ hv₀ hc₁ hv₁ hxF hzF hyF hwF hxB hwB hyB hzB he₀ he₁ he₂ he₃ hlabels e s
  obtain ⟨Ψ,hΨ,hcd,hlo,_,heq⟩ := hbranch hp hq U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁
    f₀ f₁ g₀ g₁ X Y Z W A₀ A₁ D₀ D₁ hxF hzF hyF hwF hxB hwB hyB hzB he₀ he₁ he₂ he₃
  let r₀' := Prod.map (extChartAt I a₀).symm (extChartAt I a₀).symm
  have hsrcx : x∈(extChartAt I a₀).source := by simpa only [extChartAt_source] using hKU _ (hc x)
  have hsrcy : y∈(extChartAt I a₀).source := by
    dsimp only [a₀]; rw [hcxy]; simpa only [extChartAt_source] using hKU _ (hc y)
  have hsrcz : z∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht1 0).1
  have hsrcw : w∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht4 0).1
  have hx : r₀' (X,Y)=(x,y) := Prod.ext ((extChartAt I a₀).left_inv hsrcx) ((extChartAt I a₀).left_inv hsrcy)
  have hz : r₀' (Ψ (X,Y))=(z,w) := by
    rw [hΨ]; exact Prod.ext ((extChartAt I a₀).left_inv hsrcz) ((extChartAt I a₀).left_inv hsrcw)
  have hXi : X∈interior (range I) := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply] using (hsafe 0).1 (mem_closedBall_self hρ)
  have hYi : Y∈interior (range I) := by
    dsimp only [Y,a₀]; rw [hcxy]
    simpa only [Fin.val_zero,Function.iterate_zero_apply] using (hsafe 0).2.2.1 (mem_closedBall_self hρ)
  have hZi : Z∈interior (range I) := by
    apply (hsafe 0).1
    exact mem_closedBall.mpr (by simpa only [Fin.val_zero,Function.iterate_zero_apply,dist_eq_norm] using (ht1 0).2)
  have hWi : W∈interior (range I) := by
    apply (hsafe 0).2.1
    exact mem_closedBall.mpr (by simpa only [Fin.val_zero,Function.iterate_zero_apply,dist_eq_norm] using (ht4 0).2)
  have hct := (ChartDensity.pair_inverse_germ I a₀ (X,Y)
    ((extChartAt I a₀).map_source hsrcx) ((extChartAt I a₀).map_source hsrcy) hXi hYi).1
  have hco : ContinuousAt r₀' (Z,W) := (ChartDensity.pair_inverse_germ I a₀ (Z,W)
    ((extChartAt I a₀).map_source hsrcz) ((extChartAt I a₀).map_source hsrcw) hZi hWi).1
  have hctΨ : ContinuousAt (r₀' ∘ Ψ) (X,Y) := (hΨ ▸ hco).comp hcd.continuousAt
  have heq' := original_equations_germ I S a c P hPc Wf Wb a₀ x y n b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁
    hb₀ hz₀ hb₁ hz₁ hc₀ hv₀ hc₁ hv₁ Ψ (X,Y) hlabels heq
  have hag := hgerm S c hc P L R Wf Wb n ρ δ Φ r₀' (r₀' ∘ Ψ) (X,Y)
    hct hctΨ hρ hρr hρδ (by simpa only [hx] using hsafe)
    (by simpa only [Function.comp_apply,hx,hz] using ht1)
    (by simpa only [Function.comp_apply,hx,hz] using ht2)
    (by simpa only [Function.comp_apply,hx,hz] using ht3)
    (by simpa only [Function.comp_apply,hx,hz] using ht4) huniq hsecond heq'
  refine ⟨Ψ,(hcd.differentiableAt (by simp)).hasFDerivAt,hlo,?_⟩
  apply ChartDensity.retained_pair_germ I a₀ G Φ Ψ (X,Y) hcd.continuousAt
    ((extChartAt I a₀).map_source hsrcx) ((extChartAt I a₀).map_source hsrcy) hXi hYi
  · simpa only [hΨ] using (extChartAt I a₀).map_source hsrcz
  · simpa only [hΨ] using (extChartAt I a₀).map_source hsrcw
  · simpa only [hΨ] using hZi
  · simpa only [hΨ] using hWi
  · filter_upwards [hag] with t ht
    intro htG
    exact ht (hG _ htG).1 (hG _ htG).2.1 (hG _ htG).2.2
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Fixed old-chart endpoint families give the actual retained-set relative germ. -/
theorem family_original_germ_uniform (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0<r ∧ 1≤C ∧ 0<β ∧
      ∀ {p q : ℕ},p≤d → q≤d →
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ≤r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
          OriginalEndpointControl I S a c n ρ β (Wf (P x,P (S^[n] x))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) x →
          OriginalEndpointControl I S a c n ρ β (Wf (P y,P (S^[n] y))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) y →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P x,P (S.symm^[n] x))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) x →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P y,P (S.symm^[n] y))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) y →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  obtain ⟨r,C,β,hr,hC,hβ,hh⟩ := controlled_original_germ_uniform I hclosed a K hK hKU
  refine ⟨r,C,β,hr,hC,hβ,?_⟩
  intro p q hp hq A J S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    z w ht1 ht2 ht3 ht4 a₀ X Y U V h u v hf₀ hf₁ hb₀ hb₁ he₀ he₁ he₂ he₃ hlabels e s
  obtain ⟨b₀,r₀,A₀,hbF₀,hzF₀,hmF₀⟩ := hf₀
  obtain ⟨b₁,r₁,A₁,hbF₁,hzF₁,hmF₁⟩ := hf₁
  obtain ⟨c₀,s₀,D₀,hbB₀,hzB₀,hmB₀⟩ := hb₀
  obtain ⟨c₁,s₁,D₁,hbB₁,hzB₁,hmB₁⟩ := hb₁
  have hsrc (x : M) : x∈(chartAt H (a (c x))).source := hKU _ (hc x)
  have hx : x∈(extChartAt I a₀).source := by simpa only [extChartAt_source] using hsrc x
  have hy : y∈(extChartAt I a₀).source := by dsimp only [a₀]; rw [hcxy]; simpa only [extChartAt_source] using hsrc y
  have hz : z∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht1 0).1
  have hw : w∈(extChartAt I a₀).source := by
    simpa only [Fin.val_zero,Function.iterate_zero_apply,extChartAt_source] using (ht4 0).1
  have hfx := hmF₀ x (originalTube_self I S a c hρ x hsrc)
  have hfy := hmF₁ y (originalTube_self I S a c hρ y hsrc)
  have hbx := hmB₀ x (originalTube_self I S.symm a c hρ x hsrc)
  have hby := hmB₁ y (originalTube_self I S.symm a c hρ y hsrc)
  have hfw := hmF₁ w ht3
  have hbz := hmB₁ z ht2
  rw [←hcxy] at hfy hby hfw hbz
  exact hh hp hq S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρr hρδ hG huniq hsecond hsafe
    ht1 ht2 ht3 ht4 U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ A₀ A₁ D₀ D₁
    hbF₀ hzF₀ hbF₁ hzF₁ hbB₀ hzB₀ hbB₁ hzB₁
    hfx (hmF₀ z ht1) hfy hfw hbx (hmB₀ w ht4) hby hbz
    (originalEndpoint_coordinates I S a c n a₀ x z _ b₀ r₀ hbF₀ hzF₀ hx hz he₀)
    (originalEndpoint_coordinates I S a c n a₀ y w _ b₁ r₁ hbF₁ hzF₁ hy hw he₁)
    (originalEndpoint_coordinates I S.symm a c n a₀ x w _ c₀ s₀ hbB₀ hzB₀ hx hw he₂)
    (originalEndpoint_coordinates I S.symm a c n a₀ y z _ c₁ s₁ hbB₁ hzB₁ hy hz he₃) hlabels
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Both original endpoint families from a SINGLE bilateral gauge. The inverse
family uses exactly its reversed gauge, not an unrelated certificate. All
constants precede ranks, labels, gauges, and the common starting bases. -/
theorem bilateral_endpoint_control (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ rF K₀F CreF C₁F rB K₀B CreB C₁B : ℝ,
      0<rF ∧ 1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧ 0<rB ∧ 1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧
      ∀ {p q : ℕ} (c : M → ι) (x : M) (n : ℕ) (b R C δ β γ g : ℝ)
        (A : BilateralGauge I S a c n (Dg*(b*n)) R x)
        (T : Finset (Fin d)) (_ : T.card=p) (_ : Tᶜ.card=q),
        (∀ z,z∈L (c z)) → 0≤b → 1≤b*n → 0≤R → 0≤g → 0≤C → 0≤δ →
        (∀ j∈T,γ+g≤A.lam j) → (∀ j∉T,A.lam j≤γ-g) →
        let ρ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        K₀F*ρ≤1 → ρ≤rF → K₀B*ρ≤1 → ρ≤rB →
        (∀ t : Fin (n+1),closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I)) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior p B‖≤C*(max 1 ‖B‖)^p) →
        (∀ B : E₀ →L[ℝ] E₀,‖exterior q B‖≤C*(max 1 ‖B‖)^q) →
        ∀ (Wf Wb U V : Submodule ℝ E₀),Module.finrank ℝ Wf=p → Module.finrank ℝ Wb=q →
        (‖(A.forwardSpace I S a c n T).starProjection-Wf.starProjection‖≤1/2) →
        (‖(A.backwardSpace I S a c n Tᶜ).starProjection-Wb.starProjection‖≤1/2) →
        (‖(A.forwardSpace I S a c 0 T).starProjection-U.starProjection‖≤δ) →
        (‖(A.forwardSpace I S a c 0 Tᶜ).starProjection-V.starProjection‖≤δ) →
        ∀ (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
        EndpointBudget.admissible d p Dg R C K₀F CreF C₁F b n g δ β →
        EndpointBudget.admissible d q Dg R C K₀B CreB C₁B b n g δ β →
        OriginalEndpointControl I S a c n ρ β Wf (fun i => (u i:E₀)) (fun i => (v i:E₀)) x ∧
        OriginalEndpointControl I S.symm a c n ρ β Wb (fun i => (v i:E₀)) (fun i => (u i:E₀)) x := by
  obtain ⟨rF,K₀F,CreF,C₁F,hrF,hKF,hCrF,hCF,hF⟩ := gauge_endpoint_family I hclosed S a L hL hLU Dg hDg
  obtain ⟨rB,K₀B,CreB,C₁B,hrB,hKB,hCrB,hCB,hB⟩ := gauge_endpoint_family I hclosed S.symm a L hL hLU Dg hDg
  refine ⟨rF,K₀F,CreF,C₁F,rB,K₀B,CreB,C₁B,hrF,hKF,hCrF,hCF,hrB,hKB,hCrB,hCB,?_⟩
  intro p q c x n b R C δ β γ g A T hTp hTq hc hb hbn hR hg hC hδ hf hs ρ hρF hrF' hρB hrB'
    hsafe hpolyF hpolyB Wf Wb U V hdimF hdimB hendF hendB hstartF hstartB u v hbudF hbudB
  constructor
  · exact hF c x n b R C δ β γ g A T hTp hc hb hbn hR hg hC hδ hf hs hρF hrF'
      (fun t => (hsafe t).1) hpolyF Wf U V hdimF hendF hstartF hstartB u v hbudF
  · have hf' (j : Fin d) (hj : j∈Tᶜ) : -γ+g≤(A.reverse I S a c).lam j := by
      have h := hs j (Finset.mem_compl.mp hj)
      change -γ+g≤ -A.lam j
      linarith
    have hs' (j : Fin d) (hj : j∉Tᶜ) : (A.reverse I S a c).lam j≤ -γ-g := by
      have h := hf j (by simpa only [Finset.mem_compl,not_not] using hj)
      change -A.lam j≤ -γ-g
      linarith
    apply hB c x n b R C δ β (-γ) g (A.reverse I S a c) Tᶜ hTq hc hb hbn hR hg hC hδ
      hf' hs' hρB hrB' (fun t => (hsafe t).2) hpolyB Wb V U hdimB
    · simpa only [BilateralGauge.reverse_forwardSpace] using hendB
    · simpa only [BilateralGauge.reverse_forwardSpace,BilateralGauge.backwardSpace_zero] using hstartB
    · simpa only [BilateralGauge.reverse_forwardSpace,BilateralGauge.backwardSpace_zero,compl_compl] using hstartF
    · exact hbudB
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set EuclideanSplitting
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (S : Diffeomorph I I M M ∞) {ι : Type*} (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x)

lemma BilateralGauge.forwardSpace_compl (t : ℕ) (T : Finset (Fin d)) :
    IsCompl (A.forwardSpace I S a c t T) (A.forwardSpace I S a c t Tᶜ) := by
  have hh := (EuclideanSplitting.splitting A.UF A.VF A.lam
    (fun t => (A.invF t).1) (fun t => (A.invF t).2) T).ranges_isCompl t
  rw [EuclideanSplitting.splitting_slow_range,EuclideanSplitting.splitting_fast_range] at hh
  exact hh

/-- The common starting bases are orthonormal within each actual gauge group;
no global orthogonality or conditioning of their union is postulated. -/
theorem BilateralGauge.forwardSpace_bases (t : ℕ) (T : Finset (Fin d)) :
    Nonempty (OrthonormalBasis (Fin T.card) ℝ (A.forwardSpace I S a c t T)) ∧
    Nonempty (OrthonormalBasis (Fin (d-T.card)) ℝ (A.forwardSpace I S a c t Tᶜ)) := by
  have hF : Module.finrank ℝ (A.forwardSpace I S a c t T)=T.card := finrank_groupSpace _ _ _ _ _
  have hB : Module.finrank ℝ (A.forwardSpace I S a c t Tᶜ)=d-T.card := by
    rw [show Module.finrank ℝ (A.forwardSpace I S a c t Tᶜ)=Tᶜ.card from finrank_groupSpace _ _ _ _ _]
    simp only [Finset.card_compl,Fintype.card_fin]
  exact ⟨⟨(stdOrthonormalBasis ℝ _).reindex (finCongr hF)⟩,
    ⟨(stdOrthonormalBasis ℝ _).reindex (finCongr hB)⟩⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p q : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι : Type*}
lemma OriginalEndpointControl.mono {S : Diffeomorph I I M M ∞} {a : ι → M} {c : M → ι}
    {n : ℕ} {ρ σ β : ℝ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {u : Fin p → EuclideanSpace ℝ (Fin d)} {v : Fin q → EuclideanSpace ℝ (Fin d)} {x : M}
    (h : OriginalEndpointControl I S a c n σ β W u v x) (hρ : ρ≤σ) :
    OriginalEndpointControl I S a c n ρ β W u v x := by
  obtain ⟨b,r,D,hb,hr,hg⟩ := h
  exact ⟨b,r,D,hb,hr,fun y hy => hg y (fun t => ⟨(hy t).1,(hy t).2.trans hρ⟩)⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine pair germ from three bilateral gauges in the ORIGINAL atlas.
All radii and minor tolerances precede the finite labels and the fast rank. -/
theorem gauge_original_germ_sharp (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r Cg β K₀F CreF C₁F K₀B CreB C₁B : ℝ,
      0<r ∧ 1≤Cg ∧ 0<β ∧ 1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧
      1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧
      ∀ {A J : Type*} (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (b R₀ Cext δ ε γ g ρ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        let σ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → 0≤g →
        0≤ρ → ρ≤σ → σ≤r → Cg*ρ<δ → K₀F*σ≤1 → K₀B*σ≤1 →
        (∀ p≤d,∀ B : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p B‖≤Cext*(max 1 ‖B‖)^p) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) σ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (x₀ : M) (Ar : BilateralGauge I S a c n (Dg*(b*n)) R₀ x₀)
          (Ax : BilateralGauge I S a c n (Dg*(b*n)) R₀ x)
          (Ay : BilateralGauge I S a c n (Dg*(b*n)) R₀ y)
          (Tr Tx Ty : Finset (Fin d)),Tx.card=Tr.card → Ty.card=Tr.card →
          (∀ j∈Tx,γ+g≤Ax.lam j) → (∀ j∉Tx,Ax.lam j≤γ-g) →
          (∀ j∈Ty,γ+g≤Ay.lam j) → (∀ j∉Ty,Ay.lam j≤γ-g) →
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=Tr.card →
          Module.finrank ℝ (Wf (P y,P (S^[n] y)))=Tr.card →
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-Tr.card →
          Module.finrank ℝ (Wb (P y,P (S.symm^[n] y)))=d-Tr.card →
          ‖(Ax.forwardSpace I S a c n Tx).starProjection-(Wf (P x,P (S^[n] x))).starProjection‖≤1/2 →
          ‖(Ay.forwardSpace I S a c n Ty).starProjection-(Wf (P y,P (S^[n] y))).starProjection‖≤1/2 →
          ‖(Ax.backwardSpace I S a c n Txᶜ).starProjection-(Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2 →
          ‖(Ay.backwardSpace I S a c n Tyᶜ).starProjection-(Wb (P y,P (S.symm^[n] y))).starProjection‖≤1/2 →
          ‖(Ax.forwardSpace I S a c 0 Tx).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
          ‖(Ay.forwardSpace I S a c 0 Ty).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
          ‖(Ax.forwardSpace I S a c 0 Txᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
          ‖(Ay.forwardSpace I S a c 0 Tyᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  classical
  obtain ⟨rG,Cg,β,hrG,hCg,hβ,hgerm⟩ := family_original_germ_uniform I hclosed a K hK hKU
  obtain ⟨rF,K₀F,CreF,C₁F,rB,K₀B,CreB,C₁B,hrF,hKF,hCrF,hCF,hrB,hKB,hCrB,hCB,hcontrol⟩ :=
    bilateral_endpoint_control I hclosed S a K hK hKU Dg hDg
  refine ⟨min rG (min rF rB),Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,
    lt_min hrG (lt_min hrF hrB),hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,?_⟩
  intro A J c P L R Wf Wb n b R₀ Cext δ ε γ g ρ Φ G x y σ hc hPc hcxy
    hb hbn hR₀ hCext hε hg hρ hρσ hσr hρδ hρF hρB hpoly hbudF hbudB
    hG huniq hsecond hsafe z w ht1 ht2 ht3 ht4 a₀ X Y
    x₀ Ar Ax Ay Tr Tx Ty hTx hTy hfx hsx hfy hsy hdimFx hdimFy hdimBx hdimBy
    hendFx hendFy hendBx hendBy hstartFx hstartFy hstartBx hstartBy he₀ he₁ he₂ he₃ hlabels e s
  let U := Ar.forwardSpace I S a c 0 Tr
  let V := Ar.forwardSpace I S a c 0 Trᶜ
  have hcompl : IsCompl U V := Ar.forwardSpace_compl I S a c 0 Tr
  obtain ⟨⟨u⟩,⟨v⟩⟩ := Ar.forwardSpace_bases I S a c 0 Tr
  have hp : Tr.card≤d := by simpa using Tr.card_le_univ
  have hq : d-Tr.card≤d := Nat.sub_le _ _
  have hTx' : Txᶜ.card=d-Tr.card := by simp only [Finset.card_compl,Fintype.card_fin,hTx]
  have hTy' : Tyᶜ.card=d-Tr.card := by simp only [Finset.card_compl,Fintype.card_fin,hTy]
  have hρrG := hρσ.trans (hσr.trans (min_le_left _ _))
  have hρrF := hσr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρrB := hσr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcx := hcontrol c x n b R₀ Cext ε β γ g Ax Tx hTx hTx' hc hb hbn hR₀ hg hCext hε
    hfx hsx hρF hρrF hρB hρrB (fun t => ⟨(hsafe t).1,(hsafe t).2.1⟩)
    (hpoly _ hp) (hpoly _ hq) (Wf (P x,P (S^[n] x))) (Wb (P x,P (S.symm^[n] x))) U V
    hdimFx hdimBx hendFx hendBx hstartFx hstartBx u v (hbudF _ hp) (hbudB _ hq)
  have hcy := hcontrol c y n b R₀ Cext ε β γ g Ay Ty hTy hTy' hc hb hbn hR₀ hg hCext hε
    hfy hsy hρF hρrF hρB hρrB (fun t => ⟨(hsafe t).2.2.1,(hsafe t).2.2.2⟩)
    (hpoly _ hp) (hpoly _ hq) (Wf (P y,P (S^[n] y))) (Wb (P y,P (S.symm^[n] y))) U V
    hdimFy hdimBy hendFy hendBy hstartFy hstartBy u v (hbudF _ hp) (hbudB _ hq)
  have hsafeρ : ∀ t : Fin (n+1),
      closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
      closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
      closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
      closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I) := by
    intro t
    exact ⟨(closedBall_subset_closedBall hρσ).trans (hsafe t).1,
      (closedBall_subset_closedBall hρσ).trans (hsafe t).2.1,
      (closedBall_subset_closedBall hρσ).trans (hsafe t).2.2.1,
      (closedBall_subset_closedBall hρσ).trans (hsafe t).2.2.2⟩
  exact hgerm hp hq S c P L R Wf Wb n ρ δ Φ G x y hc hPc hcxy hρ hρrG hρδ
    hG huniq hsecond hsafeρ ht1 ht2 ht3 ht4 U V hcompl u v
    (hcx.1.mono I hρσ) (hcy.1.mono I hρσ) (hcx.2.mono I hρσ) (hcy.2.mono I hρσ) he₀ he₁ he₂ he₃ hlabels
end SmoothObstruction.ManifoldCoordinates

end

end OAI
