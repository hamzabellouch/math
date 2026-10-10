import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block4Part11

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

def node384 : Integer.Sparse (Fin 2886) := [(664, 628876224), (668, -628876224), (670, -628876224), (691, 628876224), (1807, -295215840), (1811, -295215840), (1816, 590431680), (1836, 295215840), (1839, 295215840), (1844, -295215840), (1845, -295215840)]

theorem node384_check : node384 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2183598) entry_18_9) (Integer.Sparse.scale (-2050110) entry_18_10) := by decide +kernel

theorem node384_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node384 x = (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) := by
  rw [node384_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node385 : Integer.Sparse (Fin 2886) := [(664, 628876224), (668, -628876224), (670, -628876224), (691, 628876224), (1770, 7586208), (1773, 7586208), (1778, -15172416), (1807, -295215840), (1811, -295215840), (1816, 590431680), (1836, 295215840), (1839, 295215840), (1844, -295215840), (1845, -295215840), (1981, -7586208), (1985, -7586208), (1990, 7586208), (1991, 7586208)]

theorem node385_check : node385 =
    Integer.Sparse.merge (Integer.Sparse.scale (52682) entry_18_8) node384 := by decide +kernel

theorem node385_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node385 x = (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x)) := by
  rw [node385_check, Integer.Sparse.eval_merge]
  rw [node384_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node386 : Integer.Sparse (Fin 2886) := [(52, 38106432), (59, -66686256), (62, -38106432), (74, 66686256), (609, 76212864), (612, -47633040), (614, -76212864), (623, 47633040), (664, 628876224), (668, -628876224), (670, -628876224), (691, 628876224), (1770, 7586208), (1773, 7586208), (1778, -15172416), (1806, 97491312), (1807, -295215840), (1811, -295215840), (1812, 97491312), (1816, 590431680), (1819, -194982624), (1835, -97491312), (1836, 295215840), (1839, 295215840), (1840, -97491312), (1844, -295215840), (1845, -295215840), (1848, 97491312), (1849, 97491312), (1894, -95592096), (1899, 95592096), (1900, 95592096), (1916, -95592096), (1981, -7586208), (1985, -7586208), (1990, 7586208), (1991, 7586208)]

theorem node386_check : node386 =
    Integer.Sparse.merge node383 node385 := by decide +kernel

theorem node386_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node386 x = ((((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) + (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x))) := by
  rw [node386_check, Integer.Sparse.eval_merge]
  rw [node383_eval, node385_eval]

def node387 : Integer.Sparse (Fin 2886) := [(48, 77271264), (50, 77271264), (52, 38106432), (57, -231813792), (59, -66686256), (62, -38106432), (74, 66686256), (109, -67612356), (115, 77271264), (172, -38635632), (173, 67612356), (607, 38635632), (608, 496360368), (609, 76212864), (610, 496360368), (611, 38635632), (612, -47633040), (613, -992720736), (614, -76212864), (623, 47633040), (664, 628876224), (668, -628876224), (670, -628876224), (691, 628876224), (741, -48294540), (742, -496360368), (743, -496360368), (744, -77271264), (745, 496360368), (747, 496360368), (748, 38635632), (749, 48294540), (1769, 173910096), (1770, 7586208), (1772, 651865824), (1773, 7586208), (1774, 173910096), (1777, -651865824), (1778, -15172416), (1779, -651865824), (1781, -347820192), (1790, 651865824), (1806, 97491312), (1807, -295215840), (1808, 221140800), (1811, -295215840), (1812, 97491312), (1816, 590431680), (1819, -194982624), (1835, -97491312), (1836, 295215840), (1837, -110570400), (1838, -110570400), (1839, 295215840), (1840, -97491312), (1844, -295215840), (1845, -295215840), (1848, 97491312), (1849, 97491312), (1894, -95592096), (1899, 95592096), (1900, 95592096), (1914, -110570400), (1916, -95592096), (1917, -110570400), (1980, -173910096), (1981, -7586208), (1983, 110570400), (1984, 110570400), (1985, -7586208), (1986, -173910096), (1990, 7586208), (1991, 7586208), (1994, 173910096), (1998, 173910096)]

theorem node387_check : node387 =
    Integer.Sparse.merge node381 node386 := by decide +kernel

theorem node387_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node387 x = (((((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) + ((((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) + (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x)))) := by
  rw [node387_check, Integer.Sparse.eval_merge]
  rw [node381_eval, node386_eval]

def node388 : Integer.Sparse (Fin 2886) := [(311, 72769824), (313, 72769824), (318, -145539648), (461, -72769824), (467, 72769824), (589, -72769824), (590, 72769824), (1772, 1213337088), (1777, -606668544), (1779, -606668544), (1989, -606668544), (1992, -606668544), (2020, 606668544), (2021, 606668544)]

theorem node388_check : node388 =
    Integer.Sparse.merge (Integer.Sparse.scale (505346) entry_18_11) (Integer.Sparse.scale (-4212976) entry_18_12) := by decide +kernel

theorem node388_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node388 x = (((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) := by
  rw [node388_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node389 : Integer.Sparse (Fin 2886) := [(1835, -263016288), (1836, 1801279584), (1839, 1801279584), (1840, -263016288), (1844, -1801279584), (1845, -1801279584), (1848, 263016288), (1849, 263016288), (1912, 263016288), (1913, -1801279584), (1918, -1801279584), (1919, 263016288), (1921, 1801279584), (1924, 1801279584), (1926, -263016288), (1927, -263016288)]

theorem node389_check : node389 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1826502) entry_18_14) (Integer.Sparse.scale (12508886) entry_18_15) := by decide +kernel

theorem node389_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node389 x = (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x) := by
  rw [node389_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node390 : Integer.Sparse (Fin 2886) := [(1819, 50429664), (1835, -263016288), (1836, 1801279584), (1839, 1801279584), (1840, -263016288), (1844, -1801279584), (1845, -1801279584), (1848, 237801456), (1849, 237801456), (1912, 263016288), (1913, -1801279584), (1918, -1801279584), (1919, 263016288), (1921, 1801279584), (1924, 1801279584), (1926, -288231120), (1927, -288231120), (1996, 25214832), (1997, 25214832)]

theorem node390_check : node390 =
    Integer.Sparse.merge (Integer.Sparse.scale (-175103) entry_18_13) node389 := by decide +kernel

theorem node390_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node390 x = (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) := by
  rw [node390_check, Integer.Sparse.eval_merge]
  rw [node389_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node391 : Integer.Sparse (Fin 2886) := [(311, 72769824), (313, 72769824), (318, -145539648), (461, -72769824), (467, 72769824), (589, -72769824), (590, 72769824), (1772, 1213337088), (1777, -606668544), (1779, -606668544), (1819, 50429664), (1835, -263016288), (1836, 1801279584), (1839, 1801279584), (1840, -263016288), (1844, -1801279584), (1845, -1801279584), (1848, 237801456), (1849, 237801456), (1912, 263016288), (1913, -1801279584), (1918, -1801279584), (1919, 263016288), (1921, 1801279584), (1924, 1801279584), (1926, -288231120), (1927, -288231120), (1989, -606668544), (1992, -606668544), (1996, 25214832), (1997, 25214832), (2020, 606668544), (2021, 606668544)]

theorem node391_check : node391 =
    Integer.Sparse.merge node388 node390 := by decide +kernel

theorem node391_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node391 x = ((((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) + (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x))) := by
  rw [node391_check, Integer.Sparse.eval_merge]
  rw [node388_eval, node390_eval]

def node392 : Integer.Sparse (Fin 2886) := [(663, 584419104), (665, 584419104), (667, -584419104), (672, -649354560), (674, -519483648), (675, -584419104), (685, -38917440), (695, 1168838208), (706, 38917440), (734, 38917440), (812, -38917440)]

theorem node392_check : node392 =
    Integer.Sparse.merge (Integer.Sparse.scale (135130) entry_18_17) (Integer.Sparse.scale (4058466) entry_18_18) := by decide +kernel

theorem node392_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node392 x = (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x) := by
  rw [node392_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node393 : Integer.Sparse (Fin 2886) := [(663, 584419104), (665, 584419104), (667, -584419104), (672, -649354560), (674, -519483648), (675, -584419104), (685, -38917440), (695, 1168838208), (706, 38917440), (734, 38917440), (812, -38917440), (1810, 1874497536), (1815, -937248768), (1817, -937248768), (1843, -937248768), (1846, -937248768), (1866, 937248768), (1867, 937248768)]

theorem node393_check : node393 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6508672) entry_18_16) node392 := by decide +kernel

theorem node393_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node393 x = (((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) := by
  rw [node393_check, Integer.Sparse.eval_merge]
  rw [node392_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node394 : Integer.Sparse (Fin 2886) := [(669, 14344176), (671, 11953480), (673, -14344176), (676, -14344176), (677, -11953480), (687, -71720880), (690, -7172088), (692, -7172088), (693, 21516264), (694, 26297656), (698, 7172088), (708, 64548792), (732, 7172088), (735, 59767400), (746, -28688352), (813, -57376704), (1893, 915885504), (1895, 915885504), (1898, -915885504), (1901, -915885504), (1903, -915885504), (1904, -915885504), (1923, 1831771008)]

theorem node394_check : node394 =
    Integer.Sparse.merge (Integer.Sparse.scale (298837) entry_18_20) (Integer.Sparse.scale (6360316) entry_18_21) := by decide +kernel

theorem node394_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node394 x = (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x) := by
  rw [node394_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node395 : Integer.Sparse (Fin 2886) := [(554, -84246048), (555, 84246048), (557, 84246048), (560, -84246048), (669, 14344176), (671, 11953480), (673, -14344176), (676, -14344176), (677, -11953480), (687, -71720880), (690, -7172088), (692, -7172088), (693, 21516264), (694, 26297656), (698, 7172088), (708, 64548792), (732, 7172088), (735, 59767400), (746, -28688352), (813, -57376704), (1893, 915885504), (1895, 915885504), (1898, -915885504), (1901, -915885504), (1903, -915885504), (1904, -915885504), (1923, 1831771008)]

theorem node395_check : node395 =
    Integer.Sparse.merge (Integer.Sparse.scale (292521) entry_18_19) node394 := by decide +kernel

theorem node395_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node395 x = (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x)) := by
  rw [node395_check, Integer.Sparse.eval_merge]
  rw [node394_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node396 : Integer.Sparse (Fin 2886) := [(554, -84246048), (555, 84246048), (557, 84246048), (560, -84246048), (663, 584419104), (665, 584419104), (667, -584419104), (669, 14344176), (671, 11953480), (672, -649354560), (673, -14344176), (674, -519483648), (675, -584419104), (676, -14344176), (677, -11953480), (685, -38917440), (687, -71720880), (690, -7172088), (692, -7172088), (693, 21516264), (694, 26297656), (695, 1168838208), (698, 7172088), (706, 38917440), (708, 64548792), (732, 7172088), (734, 38917440), (735, 59767400), (746, -28688352), (812, -38917440), (813, -57376704), (1810, 1874497536), (1815, -937248768), (1817, -937248768), (1843, -937248768), (1846, -937248768), (1866, 937248768), (1867, 937248768), (1893, 915885504), (1895, 915885504), (1898, -915885504), (1901, -915885504), (1903, -915885504), (1904, -915885504), (1923, 1831771008)]

theorem node396_check : node396 =
    Integer.Sparse.merge node393 node395 := by decide +kernel

theorem node396_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node396 x = ((((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) + (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x))) := by
  rw [node396_check, Integer.Sparse.eval_merge]
  rw [node393_eval, node395_eval]

def node397 : Integer.Sparse (Fin 2886) := [(311, 72769824), (313, 72769824), (318, -145539648), (461, -72769824), (467, 72769824), (554, -84246048), (555, 84246048), (557, 84246048), (560, -84246048), (589, -72769824), (590, 72769824), (663, 584419104), (665, 584419104), (667, -584419104), (669, 14344176), (671, 11953480), (672, -649354560), (673, -14344176), (674, -519483648), (675, -584419104), (676, -14344176), (677, -11953480), (685, -38917440), (687, -71720880), (690, -7172088), (692, -7172088), (693, 21516264), (694, 26297656), (695, 1168838208), (698, 7172088), (706, 38917440), (708, 64548792), (732, 7172088), (734, 38917440), (735, 59767400), (746, -28688352), (812, -38917440), (813, -57376704), (1772, 1213337088), (1777, -606668544), (1779, -606668544), (1810, 1874497536), (1815, -937248768), (1817, -937248768), (1819, 50429664), (1835, -263016288), (1836, 1801279584), (1839, 1801279584), (1840, -263016288), (1843, -937248768), (1844, -1801279584), (1845, -1801279584), (1846, -937248768), (1848, 237801456), (1849, 237801456), (1866, 937248768), (1867, 937248768), (1893, 915885504), (1895, 915885504), (1898, -915885504), (1901, -915885504), (1903, -915885504), (1904, -915885504), (1912, 263016288), (1913, -1801279584), (1918, -1801279584), (1919, 263016288), (1921, 1801279584), (1923, 1831771008), (1924, 1801279584), (1926, -288231120), (1927, -288231120), (1989, -606668544), (1992, -606668544), (1996, 25214832), (1997, 25214832), (2020, 606668544), (2021, 606668544)]

theorem node397_check : node397 =
    Integer.Sparse.merge node391 node396 := by decide +kernel

theorem node397_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node397 x = (((((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) + (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x))) + ((((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) + (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x)))) := by
  rw [node397_check, Integer.Sparse.eval_merge]
  rw [node391_eval, node396_eval]

def node398 : Integer.Sparse (Fin 2886) := [(48, 77271264), (50, 77271264), (52, 38106432), (57, -231813792), (59, -66686256), (62, -38106432), (74, 66686256), (109, -67612356), (115, 77271264), (172, -38635632), (173, 67612356), (311, 72769824), (313, 72769824), (318, -145539648), (461, -72769824), (467, 72769824), (554, -84246048), (555, 84246048), (557, 84246048), (560, -84246048), (589, -72769824), (590, 72769824), (607, 38635632), (608, 496360368), (609, 76212864), (610, 496360368), (611, 38635632), (612, -47633040), (613, -992720736), (614, -76212864), (623, 47633040), (663, 584419104), (664, 628876224), (665, 584419104), (667, -584419104), (668, -628876224), (669, 14344176), (670, -628876224), (671, 11953480), (672, -649354560), (673, -14344176), (674, -519483648), (675, -584419104), (676, -14344176), (677, -11953480), (685, -38917440), (687, -71720880), (690, -7172088), (691, 628876224), (692, -7172088), (693, 21516264), (694, 26297656), (695, 1168838208), (698, 7172088), (706, 38917440), (708, 64548792), (732, 7172088), (734, 38917440), (735, 59767400), (741, -48294540), (742, -496360368), (743, -496360368), (744, -77271264), (745, 496360368), (746, -28688352), (747, 496360368), (748, 38635632), (749, 48294540), (812, -38917440), (813, -57376704), (1769, 173910096), (1770, 7586208), (1772, 1865202912), (1773, 7586208), (1774, 173910096), (1777, -1258534368), (1778, -15172416), (1779, -1258534368), (1781, -347820192), (1790, 651865824), (1806, 97491312), (1807, -295215840), (1808, 221140800), (1810, 1874497536), (1811, -295215840), (1812, 97491312), (1815, -937248768), (1816, 590431680), (1817, -937248768), (1819, -144552960), (1835, -360507600), (1836, 2096495424), (1837, -110570400), (1838, -110570400), (1839, 2096495424), (1840, -360507600), (1843, -937248768), (1844, -2096495424), (1845, -2096495424), (1846, -937248768), (1848, 335292768), (1849, 335292768), (1866, 937248768), (1867, 937248768), (1893, 915885504), (1894, -95592096), (1895, 915885504), (1898, -915885504), (1899, 95592096), (1900, 95592096), (1901, -915885504), (1903, -915885504), (1904, -915885504), (1912, 263016288), (1913, -1801279584), (1914, -110570400), (1916, -95592096), (1917, -110570400), (1918, -1801279584), (1919, 263016288), (1921, 1801279584), (1923, 1831771008), (1924, 1801279584), (1926, -288231120), (1927, -288231120), (1980, -173910096), (1981, -7586208), (1983, 110570400), (1984, 110570400), (1985, -7586208), (1986, -173910096), (1989, -606668544), (1990, 7586208), (1991, 7586208), (1992, -606668544), (1994, 173910096), (1996, 25214832), (1997, 25214832), (1998, 173910096), (2020, 606668544), (2021, 606668544)]

theorem node398_check : node398 =
    Integer.Sparse.merge node387 node397 := by decide +kernel

theorem node398_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node398 x = ((((((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) + ((((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) + (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x)))) + (((((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) + (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x))) + ((((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) + (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x))))) := by
  rw [node398_check, Integer.Sparse.eval_merge]
  rw [node387_eval, node397_eval]

def node399 : Integer.Sparse (Fin 2886) := [(541, 4228128), (545, -4228128), (562, -4228128), (567, 4228128), (1660, -65659968), (1662, 131319936), (1664, -65659968)]

theorem node399_check : node399 =
    Integer.Sparse.merge (Integer.Sparse.scale (-227986) entry_19_0) (Integer.Sparse.scale (-14681) entry_19_1) := by decide +kernel

theorem node399_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node399 x = (((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) := by
  rw [node399_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node400 : Integer.Sparse (Fin 2886) := [(580, 3234240), (581, -3234240), (597, -3234240), (598, 3234240), (1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896)]

theorem node400_check : node400 =
    Integer.Sparse.merge (Integer.Sparse.scale (318017) entry_19_3) (Integer.Sparse.scale (-11230) entry_19_4) := by decide +kernel

theorem node400_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node400 x = (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x) := by
  rw [node400_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node401 : Integer.Sparse (Fin 2886) := [(580, 3234240), (581, -3234240), (597, -3234240), (598, 3234240), (1659, -28173312), (1663, 28173312), (1690, 28173312), (1693, -28173312), (1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896)]

theorem node401_check : node401 =
    Integer.Sparse.merge (Integer.Sparse.scale (97824) entry_19_2) node400 := by decide +kernel

theorem node401_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node401 x = (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x)) := by
  rw [node401_check, Integer.Sparse.eval_merge]
  rw [node400_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node402 : Integer.Sparse (Fin 2886) := [(541, 4228128), (545, -4228128), (562, -4228128), (567, 4228128), (580, 3234240), (581, -3234240), (597, -3234240), (598, 3234240), (1659, -28173312), (1660, -65659968), (1662, 131319936), (1663, 28173312), (1664, -65659968), (1690, 28173312), (1693, -28173312), (1755, 91588896), (1757, -91588896), (1763, -91588896), (1766, 91588896)]

theorem node402_check : node402 =
    Integer.Sparse.merge node399 node401 := by decide +kernel

theorem node402_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node402 x = ((((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) := by
  rw [node402_check, Integer.Sparse.eval_merge]
  rw [node399_eval, node401_eval]

def node403 : Integer.Sparse (Fin 2886) := [(1668, 151080480), (1672, -151080480), (1674, -151080480), (1677, 151080480), (1759, -28867392), (1761, 57734784), (1764, -28867392)]

theorem node403_check : node403 =
    Integer.Sparse.merge (Integer.Sparse.scale (-524585) entry_19_6) (Integer.Sparse.scale (-100234) entry_19_7) := by decide +kernel

theorem node403_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node403 x = (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x) := by
  rw [node403_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node404 : Integer.Sparse (Fin 2886) := [(542, 18888480), (544, -37776960), (546, 18888480), (1668, 151080480), (1672, -151080480), (1674, -151080480), (1677, 151080480), (1759, -28867392), (1761, 57734784), (1764, -28867392)]

theorem node404_check : node404 =
    Integer.Sparse.merge (Integer.Sparse.scale (65585) entry_19_5) node403 := by decide +kernel

theorem node404_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node404 x = (((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) := by
  rw [node404_check, Integer.Sparse.eval_merge]
  rw [node403_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node405 : Integer.Sparse (Fin 2886) := [(603, -83768832), (604, 167537664), (605, -83768832), (1735, 166916160), (1736, -166916160), (1738, -166916160), (1739, 166916160)]

theorem node405_check : node405 =
    Integer.Sparse.merge (Integer.Sparse.scale (-290864) entry_19_9) (Integer.Sparse.scale (-579570) entry_19_10) := by decide +kernel

theorem node405_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node405 x = (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) := by
  rw [node405_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node406 : Integer.Sparse (Fin 2886) := [(603, -83768832), (604, 167537664), (605, -83768832), (1731, -84860928), (1732, 84860928), (1735, 166916160), (1736, -166916160), (1738, -166916160), (1739, 166916160), (1750, 84860928), (1751, -84860928)]

theorem node406_check : node406 =
    Integer.Sparse.merge (Integer.Sparse.scale (294656) entry_19_8) node405 := by decide +kernel

theorem node406_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node406 x = (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x)) := by
  rw [node406_check, Integer.Sparse.eval_merge]
  rw [node405_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node407 : Integer.Sparse (Fin 2886) := [(542, 18888480), (544, -37776960), (546, 18888480), (603, -83768832), (604, 167537664), (605, -83768832), (1668, 151080480), (1672, -151080480), (1674, -151080480), (1677, 151080480), (1731, -84860928), (1732, 84860928), (1735, 166916160), (1736, -166916160), (1738, -166916160), (1739, 166916160), (1750, 84860928), (1751, -84860928), (1759, -28867392), (1761, 57734784), (1764, -28867392)]

theorem node407_check : node407 =
    Integer.Sparse.merge node404 node406 := by decide +kernel

theorem node407_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node407 x = ((((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x))) := by
  rw [node407_check, Integer.Sparse.eval_merge]
  rw [node404_eval, node406_eval]

def node408 : Integer.Sparse (Fin 2886) := [(541, 4228128), (542, 18888480), (544, -37776960), (545, -4228128), (546, 18888480), (562, -4228128), (567, 4228128), (580, 3234240), (581, -3234240), (597, -3234240), (598, 3234240), (603, -83768832), (604, 167537664), (605, -83768832), (1659, -28173312), (1660, -65659968), (1662, 131319936), (1663, 28173312), (1664, -65659968), (1668, 151080480), (1672, -151080480), (1674, -151080480), (1677, 151080480), (1690, 28173312), (1693, -28173312), (1731, -84860928), (1732, 84860928), (1735, 166916160), (1736, -166916160), (1738, -166916160), (1739, 166916160), (1750, 84860928), (1751, -84860928), (1755, 91588896), (1757, -91588896), (1759, -28867392), (1761, 57734784), (1763, -91588896), (1764, -28867392), (1766, 91588896)]

theorem node408_check : node408 =
    Integer.Sparse.merge node402 node407 := by decide +kernel

theorem node408_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node408 x = (((((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) + ((((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x)))) := by
  rw [node408_check, Integer.Sparse.eval_merge]
  rw [node402_eval, node407_eval]

def node409 : Integer.Sparse (Fin 2886) := [(451, -118344384), (458, 118344384), (480, 118344384), (485, -118344384), (1660, -77806368), (1662, 77806368), (1692, 77806368), (1695, -77806368)]

theorem node409_check : node409 =
    Integer.Sparse.merge (Integer.Sparse.scale (410918) entry_19_11) (Integer.Sparse.scale (-270161) entry_19_12) := by decide +kernel

theorem node409_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node409 x = (((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) := by
  rw [node409_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node410 : Integer.Sparse (Fin 2886) := [(1674, 84597696), (1677, -84597696), (1684, -84597696), (1686, 84597696), (1738, 82859904), (1739, -82859904), (1746, -82859904), (1747, 82859904)]

theorem node410_check : node410 =
    Integer.Sparse.merge (Integer.Sparse.scale (-293742) entry_19_14) (Integer.Sparse.scale (-287708) entry_19_15) := by decide +kernel

theorem node410_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node410 x = (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x) := by
  rw [node410_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node411 : Integer.Sparse (Fin 2886) := [(1672, 8293824), (1674, 84597696), (1677, -92891520), (1684, -84597696), (1686, 76303872), (1694, 8293824), (1738, 82859904), (1739, -82859904), (1746, -82859904), (1747, 82859904)]

theorem node411_check : node411 =
    Integer.Sparse.merge (Integer.Sparse.scale (28798) entry_19_13) node410 := by decide +kernel

theorem node411_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node411 x = (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) := by
  rw [node411_check, Integer.Sparse.eval_merge]
  rw [node410_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node412 : Integer.Sparse (Fin 2886) := [(451, -118344384), (458, 118344384), (480, 118344384), (485, -118344384), (1660, -77806368), (1662, 77806368), (1672, 8293824), (1674, 84597696), (1677, -92891520), (1684, -84597696), (1686, 76303872), (1692, 77806368), (1694, 8293824), (1695, -77806368), (1738, 82859904), (1739, -82859904), (1746, -82859904), (1747, 82859904)]

theorem node412_check : node412 =
    Integer.Sparse.merge node409 node411 := by decide +kernel

theorem node412_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node412 x = ((((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x))) := by
  rw [node412_check, Integer.Sparse.eval_merge]
  rw [node409_eval, node411_eval]

def node413 : Integer.Sparse (Fin 2886) := [(468, -30335328), (475, 60670656), (486, -30335328), (554, -84246048), (555, 84246048), (557, 84246048), (560, -84246048)]

theorem node413_check : node413 =
    Integer.Sparse.merge (Integer.Sparse.scale (-105331) entry_19_17) (Integer.Sparse.scale (292521) entry_19_18) := by decide +kernel

theorem node413_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node413 x = (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x) := by
  rw [node413_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node414 : Integer.Sparse (Fin 2886) := [(468, -30335328), (475, 60670656), (486, -30335328), (554, -84246048), (555, 84246048), (557, 84246048), (560, -84246048), (1669, -281546208), (1671, 281546208), (1676, 281546208), (1678, -281546208)]

theorem node414_check : node414 =
    Integer.Sparse.merge (Integer.Sparse.scale (-977591) entry_19_16) node413 := by decide +kernel

theorem node414_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node414 x = (((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x)) := by
  rw [node414_check, Integer.Sparse.eval_merge]
  rw [node413_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node415 : Integer.Sparse (Fin 2886) := [(556, 18626976), (559, -37253952), (566, 18626976), (1742, -244089792), (1743, 244089792), (1744, 244089792), (1748, -244089792)]

theorem node415_check : node415 =
    Integer.Sparse.merge (Integer.Sparse.scale (64677) entry_19_20) (Integer.Sparse.scale (847534) entry_19_21) := by decide +kernel

theorem node415_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node415 x = (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + ((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x) := by
  rw [node415_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
